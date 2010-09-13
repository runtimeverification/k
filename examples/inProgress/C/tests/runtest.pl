use strict;
use Time::HiRes qw(gettimeofday tv_interval);
use File::Basename;
use Text::Diff;
# use XML::Writer;

my $numArgs = $#ARGV + 1;
if ($numArgs != 1) {
	die "Not enough command line arguments"
}

my $kcc = "../dist/compile.sh";
my $gcc = "gcc -lm -Wall -Wextra -x c -O0 -U __GNUC__ -pedantic -std=c99";

my $directory = $ARGV[0];
my $testSuite = $directory;
my $outputFilename = "$directory.xml";

my $globalTests = "";
my $globalNumPassed = 0;
my $globalNumFailed = 0; # failures are tests that ran but failed
my $globalNumError = 0; # errors are tests that didn't finish running
my $globalTotalTime = 0;

my @files = <$directory/*>;
foreach my $fullFilename (@files) {
	my ($baseFilename, $dirname, $suffix) = fileparse($fullFilename,".c");
	if ($suffix ne '.c') {next;}
	my $filename = "$baseFilename$suffix";
	performTest($dirname, $baseFilename);
} 
open(OUT, ">$outputFilename"); #open for write, overwrite
print OUT "<?xml version='1.0' encoding='UTF-8' ?>\n";
print OUT "<testsuite name='$testSuite' time='$globalTotalTime'>\n";
print OUT "$globalTests";
print OUT "</testsuite>\n";
close OUT;

sub performTest {
	my ($dirname, $baseFilename) = (@_);
	my $fullFilename = "$dirname$baseFilename.c";
	#print "dirname=$dirname\n";
	#print "baseFilename=$baseFilename\n";
	my $kccFilename = "${dirname}test-$baseFilename.kcc";
	my $gccFilename = "${dirname}test-$baseFilename.gcc";
	
	my $timer = [gettimeofday];
	
	my $kccCompileOutput = `$kcc -o $kccFilename $fullFilename 2>&1`;
	my $kccCompileRetval = $?;
	if ($kccCompileRetval) {
		return reportFailure($fullFilename, $timer, "kcc failed to compile $fullFilename.\n\n$kccCompileOutput");
	}
	
	my $gccCompileOutput = `$gcc -o $gccFilename $fullFilename 2>&1`;
	my $gccCompileRetval = $?;
	if ($gccCompileRetval) {
		return reportError($fullFilename, $timer, "gcc failed to compile $fullFilename.\n\n$gccCompileOutput");
	}
	
	my $kccRunOutput = `$kccFilename 2>&1`;
	my $kccRunRetval = $?;
	
	my $gccRunOutput = `$gccFilename 2>&1`;
	my $gccRunRetval = $?;
	if (($kccRunRetval != $gccRunRetval) || ($kccRunOutput ne $gccRunOutput)){
		my $msg = "Results were not identical.\n";
		$msg .= "kcc retval=$kccRunRetval\n";
		$msg .= "gcc retval=$gccRunRetval\n";
		#my $diff = diff(\$gccRunOutput, \$kccRunOutput, { STYLE => "Unified" });
		$msg .= "(actual output elided)\n";
		return reportFailure($fullFilename, $timer, $msg);
	}
	
	return reportSuccess($fullFilename, $timer, "Success");
}

sub reportFailure {
	my ($name, $timer, $message) = (@_);
	$globalNumFailed++;
	my $inner = "<failure>$message</failure>";
	return reportAny($name, $timer, $inner);	
}
sub reportError {
	my ($name, $timer, $message) = (@_);
	$globalNumError++;
	my $inner = "<error>$message</error>";
	return reportAny($name, $timer, $inner);	
}
sub reportSuccess {
	my ($name, $timer, $message) = (@_);
	$globalNumPassed++;
	my $inner = "$message";
	return reportAny($name, $timer, $inner);	
}

sub reportAny {
	my ($name, $timer, $inner) = (@_);
	my $elapsed = tv_interval( $timer, [gettimeofday]);
	$globalTotalTime += $elapsed;
	$globalTests .= "\t<testcase name='$name' time='$elapsed'>\n";
	$globalTests .= "\t\t$inner\n";
	$globalTests .= "\t</testcase>\n";
}
#@diff -y --suppress-common-lines -I '^VOLATILE' $+


# output-%: test-%
	# @echo "Running $< ..."
	# @trap "" SIGABRT; $(COMMAND_PREFIX) ./$< 2>&1 > $@.tmp; RETURN_VALUE=$$?; echo $$RETURN_VALUE >> $@.tmp
	# @mv $@.tmp $@
	
	
  # <testcase classname="net.cars.engine.PistonTest" name="moveUp" time="0.022">
    # <error message="test timed out after 1 milliseconds" type="java.lang.Exception">java.lang.Exception: test timed out after 1 milliseconds
# </error>
  # </testcase>
  # <testcase classname="net.cars.engine.PistonTest" name="moveDown" time="0.0010" />
  # <testcase classname="net.cars.engine.PistonTest" name="checkStatus" time="0.0030">
    # <failure message="Plunger status invalid to proceed driving." type="junit.framework.AssertionFailedError">junit.framework.AssertionFailedError: Plunger status invalid to proceed driving.
	# at net.cars.engine.PistonTest.checkStatus(PistonTest.java:42)
# </failure>
  # </testcase>
  # <testcase classname="net.cars.engine.PistonTest" name="checkSpeed" time="0.0080">
    # <failure message="Plunger upward speed below specifications." type="junit.framework.AssertionFailedError">junit.framework.AssertionFailedError: Plunger upward speed below specifications.
	# at net.cars.engine.PistonTest.checkSpeed(PistonTest.java:47)
# </failure>
  # </testcase>
  # <testcase classname="net.cars.engine.PistonTest" name="lubricate" time="0.0030">
    # <failure message="Failed to lubricate the plunger." type="junit.framework.AssertionFailedError">junit.framework.AssertionFailedError: Failed to lubricate the plunger.
	# at net.cars.engine.PistonTest.lubricate(PistonTest.java:52)
# </failure>
  # </testcase>
