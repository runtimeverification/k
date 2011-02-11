use strict;
use Data::Dumper;
use XML::Parser;
use XML::Twig;
use Encode;
binmode STDOUT, ":utf8";
binmode STDIN, ":utf8";

# not handling the case of multiple cdatas 
# can use 'erase' to get rid of junk cells

#########################################################
# you may want to configure things inside this section
use constant KLIST_IDENTITY => ".List{K}";
use constant KLIST_SEPARATOR => ",, ";

# might want to return, say, "'$name"
sub nameToLabel {
	my ($name) = (@_);
	return "'$name";
}
#########################################################
my %escapeMap = (
	"\007" => '\\a',
	"\010" => '\\b',
	"\011" => '\\t',
	"\012" => '\\n',
	"\013" => '\\v',
	"\014" => '\\f',
	"\015" => '\\r',
	'"' => '\\\"',
	'\\' => '\\\\'
);

# my $xso = XML::SimpleObject->new( $parser->parsefile($file) );

my $input = join("", <STDIN>);
#print "$input\n";
# my $parser = XML::Parser->new(ErrorContext => 2, Style => "Tree");
#$parser->parse($input);
# my $xso = XML::SimpleObject->new($parser->parse($input));

my $twig = XML::Twig->new();
my $twig=XML::Twig->new(   
	twig_handlers => { 
		# title   => sub { $_->set_tag( 'h2') }, # change title tags to h2
		# para    => sub { $_->set_tag( 'p')  }, # change para to p
		Filename  => sub { $_->erase; },
		Lineno  => sub { $_->erase; },
		Byteno  => sub { $_->erase; },
		Ident  => sub { $_->erase; }, # not an identifier; it's part of a location
		# list    => \&my_list_process,          # process list elements
		# div     => sub { $_[0]->flush;     },  # output and free memory
	}
);

$twig->parse($input);
my $root = $twig->root;

#print decode_utf8(xmlToK($root));
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
	if ($label eq "RawData") {
		return rawdataToK($xso);
	}
	my @klist = ();
	foreach my $child ($xso->children){
		my $childResult = xmlToK($child);
		if ($childResult) {
			push (@klist, $childResult);
		}
	}
	return nameToLabel($label) . paren(join(KLIST_SEPARATOR, @klist));

}

sub rawdataToK {
	my ($xso) = (@_);
	my $sort = $xso->att('sort');
	my $data = "";
	
	if ($sort eq "String") {
		$data = '"' . escapeString($xso->text) . '"';
	} elsif ($sort eq "Int") {
		$data = $xso->text;
	} else {
		return "unknown raw data";
	}
	return "$sort" . paren($data) . paren(KLIST_IDENTITY);
}


sub escapeSingleCharacter {
	my ($char) = (@_);
	
	if (exists($escapeMap{$char})) {
		return $escapeMap{$char};
	} elsif ($char =~ /[\x20-\x7E]/) {
		return $char;
	} else {
		my $ord = ord($char);
		return '\\' . sprintf("%03o", $ord) ;
	}
	#if ($char =~ /[a-zA-Z0-9\[ ]|[!-\/]|[:-@]|[\]-`]|[{-~]/) {
	
	#return $char;
	#escapeMap
}

sub escapeString {
	my ($str) = (@_);
	# my $octets = encode("ascii", $str, Encode::FB_CROAK);
	#my $octets = decode('ascii', $str);
	utf8::encode($str);
	my @charArray = split(//, $str);
	my @newArray = map(escapeSingleCharacter($_), @charArray) ;
	# foreach my $char (@newArray){
		# print "$char\n";
	# }
	return join('', @newArray);
	
	# my $result = "";
	# foreach my $char (split //, $str){
		# if ($char eq '"') {
			# $result .= '\\"';
		# } elsif ($char =~ /[a-zA-Z0-9.(){} \/]/) {
			# $result .= $char;
		# } else {
			# $result .= '\\' . ord($char);
		# }
	# }
	# return $result;
}

sub paren {
	my ($str) = (@_);
	return "($str)";
}