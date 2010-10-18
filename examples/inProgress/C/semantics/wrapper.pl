use strict;
use File::Temp qw/ tempfile /;
use File::Spec::Functions qw(rel2abs);
use File::Basename;
my $distDir = dirname(rel2abs($0));
my $outputFilter = "filterOutput";

my $plainOutput = 0;
my $numArgs = $#ARGV + 1;
if ($numArgs > 0) {
	$plainOutput = $ARGV[0];
}

my $state = "start";
my $retval = -1;
my $reduced = 0;
my $haveResult = 0;
my $buffer = "";
# my $kCell = "";
# my $typeCell = "";
# my $ignoreThis = 0;
while (my $line = <STDIN>) {
	# if (!$ignoreThis){
	$buffer .= $line;
	# }
	chomp($line);
	$line =~ s/[\000-\037]\[(\d|;)+m//g; # remove ansi colors
	#print "$line\n";
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
		if ($line =~ m/< input > .* <\/ input >/){
			$reduced = 1;
		# } elsif ($line =~ m/< callStack > List\(/){
			# $ignoreThis = 1;
		# } elsif ($line =~ m/<\/ callStack >/){
			# $ignoreThis = 0;
		# } elsif ($line =~ m/< blockStack > List\(/){
			# $ignoreThis = 1;
		# } elsif ($line =~ m/<\/ blockStack >/){
			# $ignoreThis = 0;
		# } elsif ($line =~ m/< genv >/){
			# $ignoreThis = 1;
		# } elsif ($line =~ m/<\/ genv >/){
			# $ignoreThis = 0;
		# } elsif ($line =~ m/< gtypes >/){
			# $ignoreThis = 1;
		# } elsif ($line =~ m/<\/ gtypes >/){
			# $ignoreThis = 0;
		# } elsif ($line =~ m/< loopStack >/){
			# $ignoreThis = 1;
		# } elsif ($line =~ m/<\/ loopStack >/){
			# $ignoreThis = 0;
		# } elsif ($line =~ m/(< (k|\(k\)\.CellLabel) > .* <\/ \2 >)/){
		# } elsif ($line =~ m/(< k > .*)$/){
			# $kCell = $1;
		# } elsif ($line =~ m/(< type > .*)$/){
			# $typeCell = $1;
		} elsif ($line =~ m/< output > String "(.*)"\(\.List{K}\) <\/ output >/){
			my $output = $1;
			$output =~ s/\%/\%\%/g;
			$output =~ s/\\\\/\\\\\\\\/g;
			print substr(`printf "x$output"`, 1);
		} elsif ($line =~ m/< resultValue > \('tv\)\.KResultLabel\(kList\("wklist_"\)\(BaseValue (-?\d+)\(\.List\{K\}\)\),,BaseType int\(\.List\{K\}\)\) <\/ resultValue >/){
			$haveResult = 1;
			$retval = $1;
		}
	}
	
	if ($state eq "failure"){
		print "$line\n";
	}
}
if ($reduced == 0||$haveResult == 0) {
	#print "$buffer\n";
	if ($plainOutput) {
		print "$buffer\n";
	} else {
		my ($fh, $filename) = tempfile();
		print $fh "$buffer\n";
		print `$distDir/$outputFilter $filename $distDir/outputFilter.yml`;
		close $fh;
	}
	# print "-------------------------------------\n";
	# # $kCell =~ s/\(.List{K}\)//g;
	# # $kCell =~ s/Rat //g;
	# # $kCell =~ s/Base-Type //g;
	# # $kCell =~ s/Id ([^\)\(,]+)/Id\(\1\)/g;
	# # $kCell =~ s/\(([^\)]*)\)\.(?:KProperLabel|KResultLabel)(\)| )/\1\2/g;
	# #$kCell =~ s/\("_\*_"\)\.KProperLabel\(([^,\(\)]+),,([^,\(\)]+)\)/\1 * \2/g;
	# # my @lines = split(/ ~> /, $kCell);
	# # @lines = @lines[0..5];
	# # $kCell = join(" ~>\n", @lines);
	# print "\n$kCell\n";
	
	# # my @lines = split(/ ~> /, $typeCell);
	# # @lines = @lines[0..2];
	# # $typeCell = join(" ~>\n", @lines);
	# print "\n$typeCell\n";
}
exit $retval;
