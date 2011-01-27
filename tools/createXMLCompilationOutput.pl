use strict;
use Time::HiRes qw(gettimeofday tv_interval);
use File::Basename;
use Text::Diff;
use HTML::Entities;

my $unnamedTestNum = 0;

sub escape {
	my ($str) = (@_);
	return HTML::Entities::encode_entities($str);
}

sub comment {
	my ($comment) = (@_);
	print "<!-- " . escape($comment) . " -->\n";
}

# use XML::Writer;

my $numArgs = $#ARGV + 1;
if ($numArgs != 2) {
	die "Not enough command line arguments"
}

my $testSuite = $ARGV[0];

# file containing the compilation output
my $testFile = $ARGV[1];

my $globalTests = "";
my $globalNumPassed = 0;
my $globalNumFailed = 0; # failures are tests that ran but failed
my $globalNumError = 0; # errors are tests that didn't finish running
my $globalTotalTime = 0;

my $hasWarnings = hasWarnings($testFile);
if ($hasWarnings) {
	reportFailure("CompilationWarnings", 0, "Failure: output has warnings");
} else {
	reportSuccess("CompilationWarnings", 0, "Success");
}

my $hasErrors = hasErrors($testFile);
if ($hasErrors) {
	reportFailure("CompilationErrors", 0, "Failure: output has errors");
} else {
	reportSuccess("CompilationErrors", 0, "Success");
}



sub hasWarnings {
	my ($testFile) = (@_);
	
	open(IN, "$testFile") or reportError("unknown", 0, "Couldn't open file $testFile");
	while (my $line = <IN>) {
		chomp $line;
		if ($line =~ /WARNING/) {
			return 1;
		}
	}
	close(IN);
	return 0;
}
sub hasErrors {
	my ($testFile) = (@_);
	
	open(IN, "$testFile") or reportError("unknown", 0, "Couldn't open file $testFile");
	while (my $line = <IN>) {
		chomp $line;
		if ($line =~ /ERROR/) {
			return 1;
		}
	}
	close(IN);
	return 0;
}

print "<?xml version='1.0' encoding='UTF-8' ?>\n";
print "<testsuite name='$testSuite' time='$globalTotalTime'>\n";
print "$globalTests";
print "</testsuite>\n";


sub reportFailure {
	my ($name, $timer, $message) = (@_);
	$globalNumFailed++;
	$message = escape($message);
	my $inner = "<failure>$message</failure>";
	#comment "$name failed";
	return reportAny($name, $timer, $inner);	
}
sub reportError {
	my ($name, $timer, $message) = (@_);
	$globalNumError++;
	$message = escape($message);
	my $inner = "<error>$message</error>";
	#comment "$name errored";
	return reportAny($name, $timer, $inner);	
}
sub reportSuccess {
	my ($name, $timer, $message) = (@_);
	$globalNumPassed++;
	$message = escape($message);
	my $inner = "$message";
	#comment "$name passed";
	return reportAny($name, $timer, $inner);	
}


sub reportAny {
	my ($name, $time, $inner) = (@_);
	#my $elapsed = tv_interval( $timer, [gettimeofday]);
	#$globalTotalTime += $elapsed;
	$globalTests .= "\t<testcase name='$name' time='$time'>\n";
	#$globalTests .= "\t\t<measurement><name>Time</name><value>$time</value></measurement>\n";
	$globalTests .= "\t\t$inner\n";
	$globalTests .= "\t</testcase>\n";
}
#@diff -y --suppress-common-lines -I '^VOLATILE' $+


# output-%: test-%
	# @echo "Running $< ..."
	# @trap "" SIGABRT; $(COMMAND_PREFIX) ./$< 2>&1 > $@.tmp; RETURN_VALUE=$$?; echo $$RETURN_VALUE >> $@.tmp
	# @mv $@.tmp $@
	
