use strict;
use File::Basename;
my $numArgs = $#ARGV + 1;
my $startingDir = './';
if ($numArgs > 0) {
	$startingDir = $ARGV[0];
}

slurp(*STDIN, $startingDir);
print "\n";
sub slurp {
	my ($file, $path) = (@_);
	#print "path = $path\n";
	while (my $line = <$file>){
		chomp($line);
		if ($line =~ m/^\s*load\s*"?([^\s"]*)"?\s*$/) {
			#print "------\n";
			#print "$line\n";
			#print "$1\n";
			my ($filename,$dirname,$suffix) = fileparse($1,".maude");
			#print "$filename, $dirname, $suffix\n";

			$filename = "$dirname$filename.maude";
			#print "trying $filename...\n";
			if (!(-e $filename)) {
				$filename = "$path$filename";
				$dirname = $path;
			}
			#print "file = $filename\n";
			#print "dirname = $dirname\n";
			my $newFile;
			open($newFile, $filename) or die "Couldn't open file $filename\n";
			slurp($newFile, $dirname);
		} else {
			print "$line\n";
		}
	}
	print "\n";
	#print "done with $file\n";
}

