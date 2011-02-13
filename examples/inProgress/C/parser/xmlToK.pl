use strict;
use XML::Parser;
use XML::Twig;
use File::Basename;
use Encode;
use MIME::Base64;
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
	'"' => '\\"',
	'\\' => '\\\\'
);

# my $xso = XML::SimpleObject->new( $parser->parsefile($file) );

my $input = join("", <STDIN>);
#print "$input\n";
# my $parser = XML::Parser->new(ErrorContext => 2, Style => "Tree");
#$parser->parse($input);
# my $xso = XML::SimpleObject->new($parser->parse($input));

# sub replaceWith {
	# my ($elt, $label) = (@_);
	# $elt->wrap_in($label);
	# my $parent = $elt->parent;
	# $elt->erase;
	# return $parent;
# }

my %labelMap = (
	List => '_::_',
);
my $filename = "";
my $handlers = { 
	# title   => sub { $_->set_tag( 'h2') }, # change title tags to h2
	# para    => sub { $_->set_tag( 'p')  }, # change para to p
	TranslationUnit => sub { 
		my $RawData = $_->first_child('RawData');
		$filename = $RawData->text;
	},
	Filename  => sub { $_->erase; },
	Lineno  => sub { $_->erase; },
	Byteno  => sub { $_->erase; },
	Ident  => sub { $_->erase; }, # not an identifier; it's part of a location
	BlockId  => sub { $_->erase; },
	SwitchId  => sub { $_->erase; },
	CompoundLiteralId  => sub { $_->erase; },
	CaseId  => sub { $_->erase; },
	ForId  => sub { $_->erase; },
	SourceCode  => sub { $_->erase; },
	DeclarationType => sub { $_->erase; },
	Variable => sub { $_->erase; },
	Paren => sub { $_->erase; },
	Significand => sub { $_->erase; },
	Exponent => sub { $_->erase; },
	TypeQualifier => sub { $_->erase; },
	StorageSpecifier => sub { $_->erase; },
	FunctionSpecifier => sub { $_->erase; },
	Specifiers => sub { $_->erase; },
	TypeSpecifier => sub { $_->erase; },
};


foreach my $key (keys %labelMap) {
	$handlers->{$key} = sub { $_->set_tag($labelMap{$key}); };	
}

			
		
		
# AnonymousName => sub { 
	# my $anon = $_;
	# my $parent = $anon->parent;
	# my $noname = XML::Twig::Elt->new( Identifier => '#NoName' );
	# my $new_elt = 
	# <Identifier>
		# <RawData sort="String"><![CDATA[main]]></RawData>
	# </Identifier>
	
	# $parent->paste($anon->erase);
	# #$_->insert( 'Name' )->erase; 
# },
#$p->insert( table => { border=> 1}, 'tr', 'td') 
#'RawData[@sort="Int"]' => sub { $_->set_att( sort => 'Rat') },
# list    => \&my_list_process,          # process list elements
# div     => sub { $_[0]->flush;     },  # output and free memory

my $twig = XML::Twig->new();
my $twig=XML::Twig->new(   
	twig_handlers => $handlers
);

$twig->parse($input);
my $root = $twig->root;

if ($filename eq ""){
	die "Could not find the filename in the XML\n";
}
#$filename = basename($filename,  (".c"));
#print decode_utf8(xmlToK($root));
$filename = decode_base64($filename);

print "mod C-program-$filename is including C .\n";
print "op 'program-$filename : -> KLabel .\n";
print "eq _`(_`)(('program-$filename).KLabel,.List`{K`}) = ";
print xmlToK($root);
print " .\n";
print "endm\n";

# this function tries to figure out what kind of a node we're looking at, then delegates the conversion to another function
sub xmlToK {
	my ($xso) = (@_);
	# if ($xso->contains_only_text()){
		# return $xso->text;
	# }
	if (!$xso->is_pcdata()) {
		return elementToK($xso);
	} 
	# elsif ($xso->children_count == 0) {
	# } elsif ($xso->children_count == 1) {
		# return KLIST_IDENTITY;
	# }
	return "";
}

sub elementToK {
	my ($xso) = (@_);
	my $label = $xso->name();
	if ($label eq "RawData") {
		return rawdataToK($xso);
	}
	if ($label eq 'Identifier') {
		my $rawData = $xso->first_child('RawData');
		my $str = '"'  . escapeString($rawData->text) . '"';
		my $ident = 'Identifier' . paren($str);
		my $id = 'Id' . paren($ident);
		return $id . paren(KLIST_IDENTITY); 
	} elsif ($label eq 'Variadic') {
		return paren("Bool true") . paren(KLIST_IDENTITY);
	} elsif ($label eq 'NotVariadic') {
		return paren("Bool false") . paren(KLIST_IDENTITY);
	}
	my @klist = ();
	foreach my $child ($xso->children){
		my $childResult = xmlToK($child);
		if ($childResult) {
			push (@klist, $childResult);
		}
	}
	my $numElements = scalar @klist;
	if ($numElements == 0) {
		push (@klist, KLIST_IDENTITY);
	}
	return nameToLabel($label) . paren(join(KLIST_SEPARATOR, @klist));

}

sub rawdataToK {
	my ($xso) = (@_);
	my $sort = $xso->att('sort');
	my $data = "";
	
	if ($sort eq 'String') {
		$data = '"' . escapeString($xso->text) . '"';
	} elsif ($sort eq 'Int') {
		$sort = 'Rat';
		$data = $xso->text;
	}  elsif ($sort eq 'Float') {
		$sort = 'Float';
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
	my $decoded = decode_base64($str);
	# my $octets = encode("ascii", $str, Encode::FB_CROAK);
	#my $octets = decode('ascii', $str);
	utf8::encode($decoded);
	my @charArray = split(//, $decoded);
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