#!/usr/bin/env perl
use strict;
use File::Spec::Functions qw(rel2abs catfile);
use Time::HiRes qw(gettimeofday tv_interval);
use File::Basename;
use Text::Diff;
use HTML::Entities;
use XML::LibXML;

my $globalTests = "";
my $globalTotalTime;
my $KRUN = catfile($ENV{'K_BASE'},"core","krun");

# first argument is a flag, -p or -f for shouldPass or shouldFail
# second argument is a directory to test
my $numArgs = $#ARGV + 1; # +1 because there is one too few
#print "$numArgs\n";
if ($numArgs != 6) {
	die "Not precise command line arguments. Usage $0 -d <directory> -f <krun flag> -n <suitename>"
}


my $directory = $ARGV[1];
my $krunFlag = $ARGV[3];
my $testSuite = $ARGV[5];
my $outputFilename = catfile($directory,"krun-results.xml");

my @files = <$directory/*>;
foreach my $fullFilename (@files) {
	runTest($fullFilename); 
}

open(OUT, ">$outputFilename"); #open for write, overwrite
print OUT "<?xml version='1.0' encoding='UTF-8' ?>\n";
print OUT "<testsuite name='$testSuite'>\n";
print OUT "$globalTests";
print OUT "</testsuite>\n";
close OUT;


sub runTest {
  my $timer =  [gettimeofday];
  my ($fullFilename) = (@_);
	my $inputFile = "/dev/null";
	my $expectedOutputFile = $fullFilename;
	my ($baseFilename, $dirname, $suffix) = fileparse($fullFilename,qr/\.out(\.[0-9]+)?/);
	$suffix =~ /\.out(\.[0-9]+)?/;
	my $testEnding = $1;
	# print "Suffix: $suffix\n";
	my $pgmFile = catfile($dirname,"..",$baseFilename);
	my $baseTestFile = catfile($dirname,$baseFilename);
	if ($suffix eq "") { 
		#print "Skipping $fullFilename\n"; 
		next; 
	}
	#print "Processing $baseFilename version $suffix\n";
	print "$fullFilename... ";
	my $possibleInFile = "$baseTestFile.in$testEnding";
	if (-e $possibleInFile) {
		$inputFile = $possibleInFile;
	} 
	my $actualOutputFile = "$baseTestFile.stdout$testEnding";
	my $actualErrorFile = "$baseTestFile.stderr$testEnding";
	# print "$KRUN $pgmFile < $inputFile > $actualOutputFile 2> $actualErrorFile\n";
	unlink($actualOutputFile, $actualErrorFile);
	if (!-e $pgmFile) {
		return reportError($fullFilename, $timer, "Test expected file $pgmFile to exist, but it doesn't");
	}
	`$KRUN $krunFlag $pgmFile < $inputFile > $actualOutputFile 2> $actualErrorFile`;
	`echo >> $actualOutputFile`;
	if (-s $actualErrorFile) {
		my $errMsg = `cat $actualErrorFile`;
		$errMsg = "Here is the error message:\n" . "---------------\n" . $errMsg ."---------------\n";
		return reportError($fullFilename, $timer, $errMsg);
	} else {
		my $diffFile = "$baseTestFile.diff$testEnding";
		unlink ($diffFile);
		`echo | cat $expectedOutputFile - |  diff -B - $actualOutputFile  >$diffFile`;
		if (-s $diffFile) {
			my $diff = `cat $diffFile`;
			my $expected = `cat $expectedOutputFile`;
			my $message = "Here is expected:\n";
			$message .= "---------------\n";
			$message .= "$expected\n";
			$message .= "---------------\n";
			$message .= "Here is the diff:\n";
			$message .= "---------------\n";
			$message .= "$diff\n";
			$message .= "---------------\n";
			return reportFailure($fullFilename, $timer, $message);
		} else {
			return reportSuccess($fullFilename,$timer);
		}
	}
}


sub reportFailure {
	my ($name, $timer, $message) = (@_);
#	$globalNumFailed++;
	$message = encode($message);
	my $inner = "<failure>$message</failure>";
	print "failed\n";
	return reportAny($name, $timer, $inner);	
}
sub reportError {
	my ($name, $timer, $message) = (@_);
#	$globalNumError++;
	$message = encode($message);
	my $inner = "<error>$message</error>";
	print "erred\n";
	return reportAny($name, $timer, $inner);	
}
sub reportSuccess {
	my ($name, $timer, $message) = (@_);
#	$globalNumPassed++;
	$message = encode($message);
	my $inner = "$message";
	print "passed\n";
	return reportAny($name, $timer, $inner);	
}

sub reportAny {
	my ($name, $timer, $inner) = (@_);
	my $elapsed = tv_interval( $timer, [gettimeofday]);
	$globalTotalTime += $elapsed;
	$globalTests .= "\t<testcase name='$name' time='$elapsed'>\n";
#	$globalTests .= "\t\t<measurement><name>Time</name><value>$elapsed</value></measurement>\n";
	$globalTests .= "\t\t$inner\n";
	$globalTests .= "\t</testcase>\n";
}

sub encode {
	my ($str) = (@_);
	my $doc = XML::LibXML::Document->new('1.0', 'UTF-8');
	my $node = $doc->createTextNode($str);
	return $node->toString();
}
