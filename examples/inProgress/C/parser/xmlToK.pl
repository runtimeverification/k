use strict;
use Data::Dumper;
use XML::Parser;
use XML::Twig;


#########################################################
# you may want to configure things inside this section
use constant KLIST_IDENTITY => ".List{K}";
use constant KLIST_SEPARATOR => ",, ";

# might want to return, say, "'$name"
sub nameToLabel {
	my ($name) = (@_);
	return "$name";
}
#########################################################

# my $xso = XML::SimpleObject->new( $parser->parsefile($file) );

my $input = join("", <STDIN>);
#print "$input\n";
# my $parser = XML::Parser->new(ErrorContext => 2, Style => "Tree");
#$parser->parse($input);
# my $xso = XML::SimpleObject->new($parser->parse($input));

my $twig = XML::Twig->new();
$twig->parse($input);
my $root = $twig->root;

print xmlToK($root);
print "\n";



# this function tries to figure out what kind of a node we're looking at, then delegates the conversion to another function
sub xmlToK {
	my ($xso) = (@_);
	my $retval = "";
	if ($xso->contains_only_text()){
		
	}
	if (!$xso->is_pcdata()) {
		return elementToK($xso);
	}
	return "$retval";
}

sub elementToK {
	my ($xso) = (@_);
	my $label = $xso->name();
	my @klist = ();
	foreach my $child ($xso->children){
		my $childResult = xmlToK($child);
		if ($childResult) {
			push (@klist, $childResult);
		}
	}
	return nameToLabel($label) . paren(join(KLIST_SEPARATOR, @klist));

}



sub paren {
	my ($str) = (@_);
	return "($str)";
}