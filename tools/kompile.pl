#!/usr/bin/perl -w
use strict;
use File::Basename;
use File::Spec;
use Switch;

# next subroutine prints the usage message;
# $0 is initially bound to the program name, as typed
sub usage {
    print "usage: $0 (-option)* <source_file>[.kmaude] (-option)*

  Options:
  -v or -verbose : verbose mode
  -m or -maudify : only maudify, do not kompile
  -h or -help : prints this message and exit
  
  Each <source_file>.kmaude must include a module with
  the same name, but capitalized.  For example, the file
  imp.kmaude must include a module called IMP.
  
  That module, which can include other modules, should
  contain the entire definition of the language.
  
  Generated output printed in <source_file>-compiled.maude.

  If an error occurs in the compilation process (including
  any Maude warnings), the script will stop, displaying the
  input, the (possibly partially) generated output, and the
  error/warning messages reported by Maude.

" ;
}

# Prints the usage message whenever the program is called without arguments
if ($#ARGV < 0) {
    print "No arguments given\n";
    usage;
    exit(1);
}

########################
# <TOOL CONFIGURATION> #
########################

# Special chars, strings and patterns, for configuring/tuning the tool  
# Since these special chars will be used as patterns in matching        
# and since some of them have special matching meaning, we use \Q \E    

my $parentheses = "\Q{}[]()\E";

########
# PERL #
########
my $special_perl_chars  = "$parentheses\Q\\^|*+?.\$\E";

#########
# Maude #
#########
my $maude_special   = "[ $parentheses\\s_\\,\\`]";
my $maude_unspecial = "[^$parentheses\\s_\\,\\`]";
my $maude_backquoted = "(?:`\\(|`\\)|`\\{|`\\}|`\\[|`\\]|`\\,|_|[^$parentheses\\s\\,\\`])*";

#####
# K #
#####
# Pattern matched by K variables
my $kvar  = "[A-Za-z][A-Za-z0-9]*[']*";

# Pattern matched by K sorts
my $ksort = "[A-Z][A-Za-z0-9\\`]*(?:\\{[A-Za-z0-9\\`]*\\})?";

# Pattern matched by K variables
my $klabel_body = "$maude_backquoted\_$maude_backquoted";
my $klabel = "\'$klabel_body(?:[$parentheses\\s\\,])|$klabel_body(?=\\()";

# Builtin tokens
my @builtin_tokens = qw(=> = -> id: .K .List .Set .Bag .Map);

# A default freezer name, to be used as a prefix of frozen strings
my $default_freezer = "FREEZER";

# A special string that will be used for freezing substrings that need not be modified
# Choose a symbol which will never appear in any programming language or program
my $specialSymbol = "K";

my $k_tools_dir = (File::Basename::fileparse($0))[1];
my $kcompile_command = File::Spec->catfile($k_tools_dir,"kcompile.sh");

my @kmaude_keywords = qw(context rule eq configuration op ops syntax kvar sort sorts subsort subsorts including kmod endkm);
#push(@kmaude_keywords,$default_freezer);
my $kmaude_keywords_pattern = join("|",map("\\b$_\\b",@kmaude_keywords));

my $comment = join("|", (
		"---\\(.*?---\\)",
		"---.*?\$",
		"\\*\\*\\*\\(.*?\\*\\*\\*\\)",
		"\\*\\*\\*.*?\$"
));

# Top level patterns
my $top_level_pattern = join("|", (
		"kmod(?:.*?)endkm",
		"mod(?:.*?)endm",
		"fmod(?:.*?)endfm",
		"set\\s.*?\$",
		"(?:in|load)\\s+\\S+"
));

# Configuration pattern: excludes, for the spacing, from the above all those substrings matching $exclude
my $exclude = join("|",
		   "\^\\s*(?:in|load)\\s+\\S+\\s*\$",                       # in/load of a file
		   "kmod\\s+(?:\\S*(?=\\s))",                               # kmodule name
		   "including(?:.*?(?=\\s+(?=$kmaude_keywords_pattern)))",  # included module expressions
		   ":$ksort",                                               # sort declarations for other than ordinary $kvar
		   "ops?\\s+.*?(?=\\s+(?=$kmaude_keywords_pattern))",       # operation declarations
		   "$klabel",                                               # K labels
		   "rule\\s*\\[[^\\[\\]]*\\]\\s*:",                         # rule labels
		   "\\d+\\.\\d+",                                           # real numbers
		   "-\\d+"                                                  # negative integer
		   );

#print "$exclude\n";
#exit(1);

# @all_sorts will hold all defined sorts
my @all_sorts = ();

# @all_tokens will hold all defined tokens
my @all_tokens = @builtin_tokens;

my $verbose = 0;
my $kompile = 1;
my $language_module_name = "";
my $language_file_name = "";

#########################
# </TOOL CONFIGURATION> #
#########################


# Process the command arguments
foreach (@ARGV) {
    if ($language_module_name eq "?") {
	$language_module_name = $_;
    }
    elsif (/^--?h(elp)?$/) {
# Terminates with usage info when asked for help
	usage;
	exit(1);
    }
    elsif (/^--?v(erbose)?$/) {
# By default, it is not verbose
	$verbose = 1;
    }
    elsif (/^--?m(audify)?$/) {
# By default, it kompiles
	$kompile = 0;
    }
    elsif (/^--?l(ang|anguage)?$/) {
	$language_module_name = "?";
    }
    elsif (/^([^-].*?)(?:|\.kmaude)$/) {
# Removes the extension ".kmaude" to <source_file> in case it has it
# It does not remove any other extension that it may have had
# For example, lang.syntax.kmaude or lang.syntax becomes lang.syntax
# Then it calls kompile on it
	$language_file_name = $1;
    }
    else {
	print "Cannot parse \"$_\"\n";
	usage;
	exit(1);
    }
}

if ($language_file_name eq "") {
    print "No input file given\n";
    usage;
    exit(1);
}

# Maudify the file "$language_file_name.kmaude", as well as all other reachable .kmaude files
maudify_file("$language_file_name.kmaude","");
print "Data resulting from processing the language definition in $language_file_name.kmaude\n" if $verbose;
print "Sorts: @all_sorts\n" if $verbose;
print "Tokens: @all_tokens\n" if $verbose;

my $exec_status = system "$kcompile_command $language_file_name.maude $language_module_name" if $kompile;
exit($exec_status);


# The function maudify($file) does the following operations:
# 1) Maude-ifies $file in case it is a .kmaude file, generating a .maude file
# 2) It does the same recursively on each included file
# 3) Returns two references:
# - one to the list of sorts that are declared in the $file or in its included files
# - another to the list of tokens that appear in operations declared in the $file or its included files
sub maudify_file {
# increment the indentation
# Bind $file to the argument string
    my ($file,$indent) = @_;
# Only files with extensions .maude or .kmaude can be maudified
    if (! ($file =~ /\.k?maude$/)) {
	print "File $file does not have the expected extension (.maude or .kmaude)\n";
	print "Exiting.\n";
	exit(1);
    }

    print "$indent \bProcessing file $file\n" if $verbose;
# Slurp all $file into $_;
    local $/=undef; open FILE,"<",$file or die "Cannot open $file\n"; local $_ = <FILE>; close FILE;

# Getting rid of comments, maintaining the line numbers of the remaining code
	s/($comment)/
		{
			local $_=$1;
			s!\S!!gs;
			$_
		}/gsme;
	
	my $maudified = "";
	while (s/^(\s*)($top_level_pattern)(\s*)//sm) {
		(my $before, local $_, my $after) = ($1,$2,$3);
		if (m!^kmod\s+(\S+)!) {
			print "$indent \bProcessing K module $1\n" if $verbose;
			$_ = maudify_module($_);
		}
		elsif (m!^f?mod\s+(\S+)!) {
			print "$indent \bProcessing Maude module $1\n" if $verbose;
			add_sorts($_);
			add_tokens($_);
		}
		elsif (m!^(?:in|load)\s+(\S+)!) {
			maudify_file(File::Spec->catfile((fileparse($file))[1],$1),"  $indent");
			s!\.kmaude\s*$!\.maude!s;
		}
		else {
#			print "Top level pattern:\n$_\n" if $verbose;
		}
		$maudified = "$maudified$before$_$after";
	}
	
	if (/\S/) {
		print "Cannot finish processing $file\n";
		print "The following text does not parse:\n$_";
		exit(1);
	}
	
    print "$indent \bDone with processing file $file\n" if $verbose;

    if ($file =~ /\.maude/) { return; }

    my $maude_file = ($file =~ /^(.*)\.kmaude$/)[0].".maude";
    open FILE,">",$maude_file or die "Cannot write $maude_file\n";
	print FILE $maudified;
	close FILE;
}


sub maudify_module {
    (local $_) = @_;

#    print "Maudifying module with tokens @all_tokens\n";

# Step 1: Freeze all comments
#    s!(---.*?(?=$))!freeze($1)!gme;

# Step: Add to @all_sorts all sorts defined a la Maude, with "sort(s)"
	add_sorts($_);

# Step 2: Freeze on-the-fly anonymous variable declarations
    s!_(:$ksort)!?$1!;
    s!(\?:$ksort)!freeze($1,"ANONYMOUS")!ge;

# Desugar syntax N ::= Prod1 | Prod2 | ... | Prodn
# At the same time, also declare N as a sort if it is not declared already
	s!(syntax\s+.*?)(?=$kmaude_keywords_pattern)!make_ops($1)!gse;

# Step 2: Declare the on-the-fly variables
    $_ = on_the_fly_kvars($_);

# Step 3: Reduce cell notation with _ to cell notation with ...
    s!<(\s*[^\s<]+\s*)_\s*>!<$1>... !gs;
    s!<\s*_(\s*/\s*[^\s>]+\s*)>! ...<$1>!gs;

# Step 4: Declare cell labels as operations
    $_ = add_cell_label_ops($_);

# Step 5: Add the module's newly defined tokens to @tokens
    add_tokens($_);

# Step 6: Add missing spaces around tokens
    $_ = spacify($_);

# Step 7: Change .List into (.).List , etc.
    s!\.(K|List|Set|Bag|Map)([^\w\{])!(.).$1$2!gs;

# Step 8: Replace remaining _ by ? (spaces were put around _ by spacify)
    s! _ ! ? !gs;

# Step 9: Change K attributes to Maude metadata
    s!(\[[^\]]*\])!make_metadata($1)!gse;

# Step 10: Change K statements into Maude statements
    s!((?:$kmaude_keywords_pattern).*?)(?=(?:$kmaude_keywords_pattern|$))!k2maude($1)!gse;

# Step 11: Unfreeze everything still frozen
    $_ = unfreeze($_,"ANONYMOUS");
#    $_ = unfreeze($_);

    return $_;
}

sub make_ops {
	local ($_) = @_;
#print "make_ops:\n$_\n";
 	my ($spaces1,$result_sort,$spaces2,$productions,$spaces3) =  /^syntax(\s+)($ksort)(\s*)::=(.*?\S)(\s*)$/s;
#print "\$productions\n$productions\n";
	my $sort_decl = "";
	if ( ! (grep { "$_" eq "$result_sort" } @all_sorts) ) {
	    $sort_decl = "sort $result_sort";
	    push(@all_sorts, $result_sort);
	}
	my $result = "$spaces1 $sort_decl $spaces2";
	my @productions = ($productions =~ /(.*?\S.*?(?:\s\|\s|$))/gs);
#print "\@productions\n@productions\n";
	foreach my $production (@productions) {
# Removing the | separator
		$production =~ s/(\s)\|(\s)/$1$2/s;
# Getting the operation attributes, if any
		my $attributes = "";
		$production =~ s/(\[[^\[\]]*\]\s*)$/
						{
							if (op_attribute($1)) {
								$attributes = $1;
								"";
							} else {$1;}
						}/se;
# Removing the spaces before and after the actual production
		my ($space4,$space5) = ("","");
		$production =~ s/^(\s*)(.*?\S)(\s*)$/
						{
							$space4 = $1;
							$space5 = $3;
							$2
						}/se;
# Extracting the list of sorts in the production, then replacing the sorts by "_"
		my @sorts = ($production =~ m/((?:^|\s)$ksort(?=\s|$))/g);
		$production =~ s/(?:^|\s)$ksort(?=\s|$)/_/g;
		$production =~ s/\s*_\s*/_/gs;
# Replacing spaces in the production by ""
		$production =~ s/\s+/`/gs;
		$result .= ($production eq "_")
					? "$space4 subsort @sorts < $result_sort$space5 "
					: "$space4 op $production : @sorts -> $result_sort$space5$attributes ";
	}
#print "Done\n";
	return "$result$spaces3";
}


sub op_attribute {
	local ($_) = @_;
	/strict|prec|gather|metadata|latex/;
}

sub k2maude {
    local ($_) = @_;
    switch ($_) {
	case /^kmod/                    { s/kmod/mod/; }
	case /^endkm/                   { s/endkm/endm/; }
	case /^$default_freezer/        {}
	case /^kvar/                    { s/k(var.*\S)(?=\s*)/$1 ./; }
	case /^rule/                    { s/^(.*\S)(\s*)$/mb $1 : KSentence .$2/s;
					  s!(\[[^\[\]]*\]) : (KSentence)!
					    (rule_attribute($1))?": $2 $1":"$1 : $2"!se;
					  s!^mb(\s+)rule(\s+\[[^\[\]]*\]\s*:)!mb$2$1rule!s;
				        }
	case /^(context|configuration)/ { s/^(.*\S)(\s*)$/mb $1 : KSentence .$2/s; }
	else                            { s/(\S)(\s*)$/$1 .$2/s; }
    }
    return $_;
}


sub rule_attribute {
    local ($_) = @_;
    /metadata|label/;  # add more keywords/patterns to recognize rule attributes
}


# Extract the K attributes and make them Maude metadata
sub make_metadata {
    local ($_) = @_;

    my @k_attributes = ();
    s!(structural|hybrid|arity\s+\d\+|(?:seq)?strict(?:\s*\((?:\s*\d+)*\s*\))?)|metadata\s+\"([^\"]*)\"!
      push(@k_attributes, ((defined $1)?$1:$2));""!gse;
    if (@k_attributes) {
#	print "->@k_attributes<-\n";
	s!(.)\]$!"$1".(($1=~/[\s\[]/s) ? "":" ")."metadata \"@k_attributes\"\]"!se;
    }
    return $_;
}

# Extract and declare on-the-fly kvariables
sub on_the_fly_kvars {
    local ($_) = @_;
    my %kvar_decls = ();
    s/\b($kvar):($ksort)/
    {
	if ($kvar_decls{$1}) {
	    if ($kvar_decls{$1} ne $2) {
		print "ERROR: Variable $1 declared with two distinct sorts ($kvar_decls{$1} and $2)\n";
		exit(1);
	    }
	} else {
	    $kvar_decls{$1} = $2;
	}
	$1;
    }
    /gse;
    my $kvars = "";
    while (my ($key,$val) = each %kvar_decls) {
	$kvars .= "kvar $key : $val ";
    }
    s/(?=endkm)/$kvars?"$kvars ":""/se;
    return $_;
}

# If there is any configuration, get all its cell labels and declare them at the end of kmodule
sub add_cell_label_ops {
    local ($_) = @_;
    my $ops = (/configuration\s+(.*?)(?:$kmaude_keywords_pattern)/s
	       ? "ops ".join(" ",set($1 =~ /<\s*\/?\s*(.*?)\s*\*?\s*>/gs))." : -> CellLabel " : "");
    s/(?=endkm)/$ops?"$ops ":""/se;
    return $_;
}

# This subroutine returns a list of all spacifiable tokens that appear in operations defined (using op) in the argument
# By spacifiable tokens we mean ones that the tool may need to add spaces to their left and/or right
sub add_tokens {
    local $_ = shift;

# Extracting all the defined operations
    my @ops=/\sops?\s+(.*?)\s+:\s+/gms;

# Put all operations in one string
    $_ = "@ops";

# Extract all tokens that appear in operations
    my @tokens = /$maude_special?($maude_unspecial+)/g;

# Add all meaningful tokens in @tokens to @all_tokens
    @all_tokens = set(@all_tokens, grep /\W/, set(@tokens));
}

# This subroutine returns a list of all spacifiable tokens that appear in operations defined (using op) in the argument
# By spacifiable tokens we mean ones that the tool may need to add spaces to their left and/or right
sub add_sorts {
    local $_ = shift;

# Extracting all the defined sorts
    my @sorts = /\ssorts?((?:\s+$ksort)+)\s+(?=\.|$kmaude_keywords_pattern)/gs;

	@sorts = split(/\s+/, "@sorts");
	
#	print "Adding sorts: @sorts\nModule: $_\n" if $verbose;
# Add these sorts to @all_sorts
    @all_sorts = set(@all_sorts, @sorts);

# Extracting and add all sorts defined indirrectly by means of BNF grammars
#	@sorts = /\ssyntax\s+($ksort)\s+::=/gs;
#    @all_sorts = set(@all_sorts, @sorts);
}

# Next subroutine takes a string (expecte to be a kmaude module),
# and returns a string obtained from the original one by adding spaces to the left and/or
# to the right of tokens in the string; recall that the global @all_tokens holds all tokens
sub spacify {
    my ($lines) = @_;
    my %substrings;

#    print "$lines\n@tokens\n";

# Put all tokens in a string
    my $tokenString = " @all_tokens ";

# Compute a hash mapping each token to a list of pairs (before,after)
# Representing the contexts in which the token is a substring of other tokens
    foreach my $token (@all_tokens) {
		my $token_pattern = $token;
		$token_pattern =~ s/([$special_perl_chars])/\\$1/g;
#		print "\nToken $token ";
		my @pairs = ();
# Iterate through all matches of the token in the string of tokens
		while($tokenString =~ /$token_pattern/g) {
# Then extract and save the token fragments before and after the matched token
			my ($before,$after) = ($`,$');
			$before =~ s/^.* //;
			$after  =~ s/ .*$//;
			if ($before or $after) {
				$before =~ s/([$special_perl_chars])/\\$1/g;
				$after  =~ s/([$special_perl_chars])/\\$1/g;
				push(@pairs, ($before,$after));
			}
		}
# Hash the list of token contexts
		if (@pairs) {
#			print "$token : @pairs\n";
			$substrings{$token} = \@pairs;
		}
    }

# Freeze all excluded substrings, which we do NOT want to be spacified
    $lines =~ s/($exclude)/freeze($1,"EXCLUDE")/gmse;

#    print "Iterating through maximal tokens\n";
    foreach my $token (@all_tokens) {
		my $token_pattern = $token;
		$token_pattern =~ s/([$special_perl_chars])/\\$1/g;
		if (! exists $substrings{$token}) {
#	    print "$token\n";
			$lines =~ s/(.)($token_pattern)(.)/add_spaces($1,freeze($2,"EXCLUDE"),$3)/gse;
		}
    }

    while (my ($token,$valref) = each %substrings) {
#	print "Token: $token: @$valref\n";
		my $token_pattern = $token;
		$token_pattern =~ s/([$special_perl_chars])/\\$1/g;
		my @temp = @$valref;
		while ((my $before, my $after, @temp) = @temp) {
#	    print "$before!!!$after\n";
			$lines =~ s/($before$token_pattern$after)/freeze($1,"TOKEN")/gse;
		}
		$lines =~ s/(.)($token_pattern)(.)/add_spaces($1,$2,$3)/gse;
		$lines = unfreeze($lines,"TOKEN");
    }

    $lines =~ s/_/ _ /gs;

    $lines = unfreeze($lines,"EXCLUDE");

    return $lines;
}

# Adds spaces before and/or after token, if needed
sub add_spaces {
    my ($before,$token,$after) = @_;
    return ($before.(($before =~ /$maude_special/) ? "":" ").$token.(($after =~ /$maude_special/) ? "":" ").$after);
}
    

# Makes certain (sub)strings special, so that they stay "frozen" until other substitutions are complete
sub freeze {
    my $string = shift;
    my $marker = "$default_freezer\b";
    if (@_) {
	$marker = shift;
    }
    return "$marker".join("$specialSymbol",map(ord,(split('',$string))))."$specialSymbol";

#    return "$specialSymbol$marker".join("$specialSymbol$marker",map(ord,(split('',$string))));
}

# Makes concrete all the frozen (sub)strings
sub unfreeze {
    my $all = shift;
    my $marker = "$default_freezer\b";
    if (@_) {
	$marker = shift;
    }

    $all =~ s/$marker(\d+(?:$specialSymbol\d+)*)$specialSymbol/join("", map(chr, split("$specialSymbol",$1)))/gse;

    return $all;
}

# Takes a list and eliminates duplicates from it
sub set {
    my %hash = map { $_,1 } @_;
    return keys %hash;
}
