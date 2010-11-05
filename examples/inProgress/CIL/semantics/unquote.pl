use strict;
#open(MYINPUTFILE, "<quoted.maude");
# <STDIN> for standard in, <MYINPUTFILE> for a file

while(my $line = <STDIN>) {
	chomp($line);
	# first adjust whitespace and colors
	$line =~ s/'\\n /\n/g;
	$line =~ s/'\\t /\t/g;
	$line =~ s/'\\r /\r/g;
	$line =~ s/'\\[ogb] //g;
	$line =~ s/'\\s / /g;
	
	$line =~ s/metadata\((".*?")\)/metadata $1/; # removes parens from metadata
	$line =~ s/label\((.*?)\)/label $1/; # removes parens from label
	$line =~ s/prec\((\d*)\)/prec $1/; # removes parens from prec
	$line =~ s/^\s*none//; # removes none sections
	$line =~ s/nil -> /-> /; # removes nil op arguments
	my $operatorClass = '(?:(?:`[\(\)\[\]\{\},])|[^\(\)\[\]\{\}, ])';
	my $sortClass = '(?:(?:`[\{\}])|[^_\(\)\[\]\{\},\. `])';
	my $containerClass = '(?:List`\{K`\}|Set|Bag|Map|K|List)';
	my $sortTerminator = '(?:[ ,\]])';
	
	$line =~ s/'($operatorClass+)\.$containerClass($sortTerminator)/\('$1\)$2/g; # quoted constants
	# 'arithBinConversionOps.Set
	#  op ''_._ 
	$line =~ s/'($operatorClass+)\.($sortClass+)/\('$1\)\.$2/g; # quoted constants
	#$line =~ s/'([^ '"(),\]\[]+)\.([^ ,.\]\[]+)/('$1)/g; # quoted constants
	$line =~ s/'"(([^"]|([\\]["]))*?)"\.([^ ,\]])/\("$1"\)\.$4/g; # string constants
	#$line =~ s/'"(([^\\"]|([\\]["])|([\\][^"]))*?)"\.[^ ,.\]\[]+/"$1"/g; # string constants
	$line =~ s/([^ `])\[/$1\(/g; # changes [ into (
	$line =~ s/\] \./FSLENDLQQQ/; # saves attribute brackets
	while ($line =~ s/([^`])\]/$1\)/g){ } # changes ] into )
	while ($line =~ s/sorts ([^ ]*?) ;/sort $1 . sorts/g){ } # separates out sorts
	$line =~ s/FSLENDLQQQ/\] \./; # replaces attribute brackets
	$line =~ s/\[none\]//g; # remove [none] attributes
	$line =~ s/'([^ \)\(,\[\]\{\}]+)/$1/g; # removes all other quotes
	#$line =~ s/FSLOPERATORSAVEME#####([^#]*)#####/'$1/g; # replace constants
	print "$line\n";
}