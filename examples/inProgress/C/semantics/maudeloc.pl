use strict;
my $inComment = 0;

while (my $line = <STDIN>){
	chomp($line);
	while ($line =~ s/\s\s/ /g){}
	$line =~ s/\s/ /g;
	$line =~ s/^\s//g;
	$line =~ s/\s$//g;
	$line =~ s/---.*$//g;
	if (!$inComment) {
		if ($line =~ s/\*\*\*\(.*$//) {
			$inComment = 1;
		}
	} else {
		if ($line =~ s/^.*\*\*\*\)//) {
			$inComment = 0;
		}
	}
	$line =~ s/^\s*$//;
	if (!$inComment && $line) {
		print "$line\n";
	}
}
