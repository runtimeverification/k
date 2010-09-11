use strict;
my $numArgs = $#ARGV + 1;
if ($numArgs != 1) {
	die "Not enough command line arguments"
}

my $directory = $ARGV[0];
my $testSuite = $directory;
my $outputFilename = "$directory.xml";
my $totalTime = 0.5;
my $singleTime = 0.5;
my $testName = "helloworld.c";
open(OUT, ">$outputFilename"); #open for write, overwrite
print OUT "<?xml version='1.0' encoding='UTF-8' ?>\n";
print OUT "<testsuite name='$testSuite' time='$totalTime'>\n";
print OUT "<testcase name='$testName' time='$singleTime' />\n";
print OUT "</testsuite>\n";
close OUT;
