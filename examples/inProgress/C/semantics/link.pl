use strict;
use File::Basename;
my $numArgs = $#ARGV + 1;
#$startingDir = $ARGV[0];
if ($numArgs < 1) {
	die "Need to provide file names to link\n";
}

my @operators;
my @programNames;
my @programs;
foreach my $filename (@ARGV) {
	#print "$filename\n";
	open(my $newFile, $filename) or die "Couldn't open file $filename\n";

	while (my $line = <$newFile>){
		chomp($line);
		if ($line =~ m/^mod C-(program-.*) is including/) {
			# push(@programNames, "$1");
			next;
		}
		if ($line =~ m/^eq (.*?)= /) { # if we have an equation, we're done with operators
			push(@programNames, $1);
			push(@programs, $line);
			last;
		}
		push(@operators, $line);
	}
}

foreach my $operator (@operators){
	print "$operator\n";
}

foreach my $program (@programs){
	print "$program\n";
}

print "op linked-program : -> K .\n";
print "eq linked-program = ";
print '(\'_::_).KHybridLabel(';
printNested(@programNames);
print ')';

sub printNested {
	my ($name, @rest) = (@_);

	print "$name,, ";
	#print @rest;
	if ($name != @rest) {
		printNested(@rest);
	} else {
		print '.List{K}';
	}

}

# foreach my $name (@programNames){
	# print "$name ";
# }
print ".\n";

