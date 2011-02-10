use strict;
use Data::Dumper;
use XML::Parser;
use XML::Twig;

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

sub xmlToK {
	my ($xso) = (@_);
	my $retval = "";
	if (!$xso->is_ent()) {
		$retval .= $xso->name();
	}
	foreach my $child ($xso->children){
		$retval .= xmlToK($child);
	}
	return "$retval\n";
}


