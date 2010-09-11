use strict;
use Benchmark qw(:all) ;
use File::Basename;

my $numArgs = $#ARGV + 1;
if ($numArgs != 1) {
	die "Not enough command line arguments"
}

my $kcc = "../dist/compile.sh";
my $gcc = "gcc -lm -Wall -Wextra -x c -O0 -U __GNUC__ -pedantic -std=c99";

my $directory = $ARGV[0];
my $testSuite = $directory;
my $outputFilename = "$directory.xml";
my $totalTime = 0.5;
my $singleTime = 0.5;
my $testName = "helloworld.c";

my @files = <$directory/*>;
foreach my $fullFilename (@files) {
	my ($baseFilename, $dirname, $suffix) = fileparse($fullFilename,".c");
	my $filename = "$baseFilename$suffix";
	performTest($dirname, $baseFilename);
} 
open(OUT, ">$outputFilename"); #open for write, overwrite
print OUT "<?xml version='1.0' encoding='UTF-8' ?>\n";
print OUT "<testsuite name='$testSuite' time='$totalTime'>\n";
print OUT "<testcase name='$testName' time='$singleTime' />\n";
print OUT "</testsuite>\n";
close OUT;

sub performTest {
	my ($dirname, $baseFilename) = (@_);
	my $fullFilename = "$dirname$baseFilename.c";
	print "dirname=$dirname\n";
	print "baseFilename=$baseFilename\n";
	my $kccFilename = "${dirname}test-$baseFilename.kcc";
	my $gccFilename = "${dirname}test-$baseFilename.gcc";
	my $output;
	my $retval;
	
	$output = `$kcc -o $kccFilename $fullFilename 2>&1`;
	$retval = $?;
	print "output=$output\n";
	print "retval=$retval\n";
	$output = `$gcc -o $gccFilename $fullFilename 2>&1`;
	$retval = $?;
	print "output=$output\n";
	print "retval=$retval\n";
}
#@diff -y --suppress-common-lines -I '^VOLATILE' $+

# test-%.kcc: %.c $(KCC) $(PARSER)
	# @echo "Compiling $@..."
	# @$(COMMAND_PREFIX) $(KCC) -o $@ $<
	
# test-%.gcc: %.c
	# @echo "Compiling $@..."
	# @$(GCC) -o $@ $< 2> /dev/null
	
# output-%: test-%
	# @echo "Running $< ..."
	# @trap "" SIGABRT; $(COMMAND_PREFIX) ./$< 2>&1 > $@.tmp; RETURN_VALUE=$$?; echo $$RETURN_VALUE >> $@.tmp
	# @mv $@.tmp $@