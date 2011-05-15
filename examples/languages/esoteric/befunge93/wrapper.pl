#!/usr/bin/env perl
use strict;
use File::Temp qw/ tempfile /;
use File::Spec::Functions qw(rel2abs);
use File::Basename;
my @input = <>;
print maudeOutputWrapper(0, @input);
sub maudeOutputWrapper {
	my ($plainOutput, @input) = (@_);
	my $realOutput = "";
	my $state = "start";
	my $retval = -1;
	my $reduced = 0;
	my $haveResult = 0;
	my $buffer = "";
	my $haveError = 0;

	my $errorCell = "";
	my $finalComp = "";

	my $myFunc = "";
	my $myFile = "";
	my $myLine = "";
	my $myOffsetStart = "";
	my $myOffsetEnd = "";

	for my $line (@input) {
		$buffer .= $line;
		chomp($line);
		if ($state eq "start"){
			if ($line =~ m/^rewrites: /){
				$state = "rewrite";
			}
		} elsif ($state eq "rewrite"){
			if ($line =~ m/^result (?:NeBag|Bag): (.*)$/){
				$state = "success";
				$realOutput .= $1;
			} else {
				$state = "failure";
				$realOutput .= "FAILURE\n";
			}
		} elsif ($state eq "success"){
			if ($line =~ m/< result > String "(.*)"\(\.List{K}\) <\/ result >/){
				$reduced = 1;
				$haveResult = 1;
				my $output = $1;
				$output =~ s/\%/\%\%/g;
				$output =~ s/`/\\`/g;
				$output =~ s/\\\\/\\\\\\\\/g;
				$realOutput .= "===Result=======================================================================\n";
				$realOutput .= substr(`printf "x$output"`, 1) . "\n";
				$realOutput .= "===Result======================================================================\n";
			} elsif ($line =~ m/< resultProgram > String "(.*)"\(\.List{K}\) <\/ resultProgram >/){
				$reduced = 1;
				$haveResult = 1;
				my $output = $1;
				$output =~ s/\%/\%\%/g;
				$output =~ s/`/\\`/g;
				$output =~ s/\\\\/\\\\\\\\/g;
				$realOutput .= "===ResultProgram================================================================\n";
				$realOutput .= substr(`printf "x$output"`, 1) . "\n";
				$realOutput .= "===ResultProgram================================================================\n";
			} elsif ($line =~ m/< k > (.*) <\/ k >/){
				$haveError = 1;
				$finalComp = $1;
			}
		}
		
		if ($state eq "failure"){
			$realOutput .= "$line\n";
		}
	}
	if ($plainOutput) {
		$realOutput .= "$buffer\n";
	} elsif ($reduced == 0 || $haveResult == 0) {
		$realOutput .= "\n=============================================================\n";
		$realOutput .= "ERROR! encountered an error while executing this program.\n";
		my $template = "dump-XXXXXXXXXX";
		my ($fh, $filename) = tempfile($template, SUFFIX => '.kdump');
		print $fh "$buffer\n";
		if ($errorCell ne "") {
			$realOutput .= "=============================================================\n";
			$realOutput .= "$errorCell\n";
		}
		$realOutput .= "\nFull report can be found in $filename\n";
		close $fh;
	}
	return ($realOutput);
}
1;