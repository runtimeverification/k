use strict;
my $state = "start";
my $retval = -1;
my $reduced = 0;
my $haveResult = 0;
my $buffer = "";
my $profileBuffer = "";
my $profileFile = "";
my $kCell = "";
my $typeCell = "";
my $profiling = "";
my $numArgs = $#ARGV + 1;
if ($numArgs == 2) {
	my $flag = $ARGV[0];
	if ($flag eq "-p") {
		$profiling = 1;
	}
	$profileFile = $ARGV[1];
}

while (my $line = <STDIN>) {
	$buffer .= $line;
	chomp($line);
	$line =~ s/[\000-\037]\[(\d|;)+m//g; # remove ansi colors
	#print "$line\n";
	if ($profiling) {
		$profileBuffer .= "$line\n";
	}
	if ($state eq "start"){
		if ($line =~ m/^erewrite in /){
			$state = "rewrite";
			#printf "REWRITE\n";
		}
	} elsif ($state eq "rewrite"){
		$line = <STDIN>;
		$buffer .= $line;
		$line =~ s/[\000-\037]\[(\d|;)+m//g; # remove ansi colors
		#print "$line\n";
		if ($line =~ m/^result NeBag:/){
			$state = "success";
			#printf "SUCCESS\n";
		} else {
			$state = "failure";
			printf "FAILURE\n";
		}
	} elsif ($state eq "success"){
		if ($line =~ m/< (input|\(input\)\.CellLabel) > .* <\/ \1 >/){
			$reduced = 1;
		} elsif ($line =~ m/(< (k|\(k\)\.CellLabel) > .* <\/ \2 >)/){
			$kCell = $1;
		} elsif ($line =~ m/(< (type|\(type\)\.CellLabel) > .* <\/ \2 >)/){
			$typeCell = $1;
		}  elsif ($line =~ m/< (output|\(output\)\.CellLabel) > String "(.*)"\(\.List{K}\) <\/ \1 >/){
			my $output = $2;
			$output =~ s/\%/\%\%/g;
			$output =~ s/\\\\/\\\\\\\\/g;
			print substr(`printf "x$output"`, 1);
		} elsif ($line =~ m/< (resultValue|\(resultValue\)\.CellLabel) > \('tv\)\.KResultLabel\(Rat (-?\d+)\(\.List\{K\}\),,Base-Type int\(\.List\{K\}\)\) <\/ \1 >/){
			$haveResult = 1;
			$retval = $2;
		}
	} 
	
	if ($state eq "failure"){
		print "$line\n";
	}
}
if ($profiling) {
	open (MYFILE, ">$profileFile.profile");
	print MYFILE $profileBuffer;
	close (MYFILE);
}
if ($reduced == 0||$haveResult == 0) {
	print "$buffer\n";
	print "-------------------------------------\n";
	# $kCell =~ s/\(.List{K}\)//g;
	# $kCell =~ s/Rat //g;
	# $kCell =~ s/Base-Type //g;
	# $kCell =~ s/Id ([^\)\(,]+)/Id\(\1\)/g;
	# $kCell =~ s/\(([^\)]*)\)\.(?:KProperLabel|KResultLabel)(\)| )/\1\2/g;
	#$kCell =~ s/\("_\*_"\)\.KProperLabel\(([^,\(\)]+),,([^,\(\)]+)\)/\1 * \2/g;
	my @lines = split(/ ~> /, $kCell);
	@lines = @lines[0..5];
	$kCell = join(" ~>\n", @lines);
	print "\n$kCell\n";
	
	@lines = split(/ ~> /, $typeCell);
	@lines = @lines[0..2];
	$typeCell = join(" ~>\n", @lines);
	print "\n$typeCell\n";
}
exit $retval;
