#!/usr/bin/env perl
use strict;
use File::Spec::Functions qw(rel2abs catfile);
use Time::HiRes qw(gettimeofday tv_interval);
use File::Basename;
use Text::Diff;
use HTML::Entities;


my $globalTests = "";
my $KRUN = catfile($ENV{'K_BASE'},"core","krun");

# first argument is a flag, -p or -f for shouldPass or shouldFail
# second argument is a directory to test
my $numArgs = $#ARGV + 1; # +1 because there is one too few
#print "$numArgs\n";
if ($numArgs != 2) {
	die "Not precise command line arguments. Usage $0 -d <directory> "
}


my $directory = $ARGV[1];
my $testSuite = $directory;
my $outputFilename = catfile($directory,"results.xml");

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
  my ($fullFilename) = (@_);
	my $inputFile = "/dev/null";
	my $expectedOutputFile = $fullFilename;
	my ($baseFilename, $dirname, $suffix) = fileparse($fullFilename,qr/\.out(\.[0-9]+)?/);
	$suffix =~ /\.out(\.[0-9]+)?/;
  my $testEnding = $1;
  #print "Suffix: $suffix\n";
	my $pgmFile = catfile($dirname,"..",$baseFilename);
	my $baseTestFile = catfile($dirname,$baseFilename);
	if ($suffix eq "") { 
		#print "Skipping $fullFilename\n"; 
		next; 
	}
	#print "Processing $baseFilename version $suffix\n";
	if ($suffix ne ".out") {
		$inputFile = "$baseTestFile.in$testEnding";
	} 
	my $actualOutputFile = "$baseTestFile.stdout$testEnding";
	my $actualErrorFile = "$baseTestFile.stderr$testEnding";
	#print "$KRUN $pgmFile < $inputFile > $actualOutputFile 2> $actualErrorFile\n";
  unlink($actualOutputFile,$actualErrorFile);
	`$KRUN $pgmFile < $inputFile > $actualOutputFile 2> $actualErrorFile`;
	if (-s $actualErrorFile) {
		error($fullFilename);
	} else {
    my $diffFile = "$baseTestFile.diff$testEnding";
    unlink ($diffFile);
		`diff $expectedOutputFile $actualOutputFile >$diffFile`;
		if (-s $diffFile) {
			failure($fullFilename);
		} else {
			success($fullFilename);
		}
	}
}


sub error {
  my ($testFile) = (@_);
  reportError($testFile, 1, "");
}


sub failure {
  my ($testFile) = (@_);
  reportFailure($testFile, 1, "");
}


sub success {
  my ($testFile) = (@_);
  reportSuccess($testFile, 1, "");
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
	print "$name errored\n";
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
#	my $elapsed = tv_interval( $timer, [gettimeofday]);
  my $elapsed = 0;
#	$globalTotalTime += $elapsed;
	$globalTests .= "\t<testcase name='$name' time='$elapsed'>\n";
#	$globalTests .= "\t\t<measurement><name>Time</name><value>$elapsed</value></measurement>\n";
	$globalTests .= "\t\t$inner\n";
	$globalTests .= "\t</testcase>\n";
}

