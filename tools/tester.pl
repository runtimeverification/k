#!/usr/bin/env perl
use strict;
use File::Spec::Functions qw(rel2abs catfile);
use Time::HiRes qw(gettimeofday tv_interval);
use File::Basename;
use Text::Diff;
use HTML::Entities;


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
my $testSuite = $directory;
my $outputFilename = catfile($directory,"krun-results.xml");

my @files = <$directory/*>;
foreach my $fullFilename (@files) {
	runTest($fullFilename); 
}

open(OUT, ">$outputFilename"); #open for write, overwrite
print OUT "<?xml version='1.0' encoding='UTF-8' ?>\n";
print OUT "<testsuite name='$directory'>\n";
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
	my $possibleInFile = "$baseTestFile.in$testEnding";
	if (-e $possibleInFile) {
		$inputFile = $possibleInFile;
	} 
	my $actualOutputFile = "$baseTestFile.stdout$testEnding";
	my $actualErrorFile = "$baseTestFile.stderr$testEnding";
	# print "$KRUN $pgmFile < $inputFile > $actualOutputFile 2> $actualErrorFile\n";
	unlink($actualOutputFile,$actualErrorFile);
	`$KRUN $krunFlag $pgmFile < $inputFile > $actualOutputFile 2> $actualErrorFile`;
	`echo >> $actualOutputFile`;
	if (-s $actualErrorFile) {
		reportError($fullFilename,$timer);
	} else {
    my $diffFile = "$baseTestFile.diff$testEnding";
    unlink ($diffFile);\
		`echo | cat $expectedOutputFile - |  diff -B - $actualOutputFile  >$diffFile`;
		if (-s $diffFile) {
			reportFailure($fullFilename,$timer);
		} else {
			reportSuccess($fullFilename,$timer);
		}
	}
}


sub reportFailure {
	my ($name, $timer, $message) = (@_);
#	$globalNumFailed++;
	my $inner = "<failure>$message</failure>";
	print "$name failed\n";
	return reportAny($name, $timer, $inner);	
}
sub reportError {
	my ($name, $timer, $message) = (@_);
#	$globalNumError++;
	my $inner = "<error>$message</error>";
	print "$name erred\n";
	return reportAny($name, $timer, $inner);	
}
sub reportSuccess {
	my ($name, $timer, $message) = (@_);
#	$globalNumPassed++;
	my $inner = "$message";
	print "$name passed\n";
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

