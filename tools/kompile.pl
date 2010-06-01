#!/usr/bin/perl -w
use strict;
use File::Basename;
use File::Spec;
use Switch;

# next subroutine prints the usage message;
# $0 is initially bound to the program name, as typed
sub usage {
    print "
usage: $0 <source_file>[.kmaude] [<module_name>]

  If <module_name> is not specified, it is asumed to be allcaps(<source_file>).
  <source_file> must define directly or indirectly (via loading) module <module_name>.
  Module <module_name> should contain the entire definition of the language.
  Output is printed in <source_file>-compiled.maude.

  If an error occurs in the compilation process (including any Maude warnings),
  the script will stop, displaying the input, the (possibly partially) generated output,
  and the error/warning messages reported by Maude.

" ;
}

# prints the usage message whenever the program is not called with one or two arguments,
# or whenever it is called with the help option (-h, --h, -help, --help, etc.)
if ($#ARGV < 0 || $#ARGV > 1 || $ARGV[0] =~ /^--*(h|help)$/) {
    usage;
    exit;
}

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


# Adds the extension ".kmaude" to <source_file> in case it didn't have it
# It does not remove any other extension that it may have had
# For example, lang.syntax becomes lang.syntax.kmaude
my $language_file = (($ARGV[0] =~ /^(.*)\.kmaude$/) ? $1 : $ARGV[0]);

# A default freezer name, to be used as a prefix of frozen strings
my $default_freezer = "FREEZER";

# A special string that will be used for freezing substrings that need not be modified
# Choose a symbol which will never appear in any programming language or program
my $specialSymbol = "K";

my $k_tools_dir = (File::Basename::fileparse($0))[1];
my $kcompile_command = File::Spec->catfile($k_tools_dir,"kcompile.sh");

my @kmaude_keywords = qw(context rule eq configuration op ops kvar sort sorts subsort subsorts including kmod endkm);
push(@kmaude_keywords,$default_freezer);
my $kmaude_keywords_pattern = join("|",map("\\b$_\\b",@kmaude_keywords));

# Configuration pattern: matches all strings which need to be maude-ified
# Note that maudify analyzes the entire module anyway for operation names, but
# it only changes those substrings matching the $include pattern
my $include = "kmod(?:.*?)endkm|(?:in|load).*?\$";

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
#exit;

# Maudify the file "$language_file.kmaude", as well as all other reachable .kmaude files
my @tokens = maudify("$language_file.kmaude");
#print "The original language definition, $language_file.kmaude, has the following tokens: @tokens\n";

system "$kcompile_command $language_file.maude";


# The function maudify($file) does the following operations:
# 1) Maude-ifies $file in case it is a .kmaude file, generating a .maude file
# 2) It does the same recursively on each included file
# 3) Returns the list of tokens that appear in operations declared in the $file or its included files
sub maudify {
# Bind $file to the argument string
    my ($file) = @_;
# If $file has no extension, then add it the extension .maude
    if (! ($file =~ /\.k?maude$/)) {
	print "File $file does not have the expected extension (.maude or .kmaude)\n";
	print "Exiting.\n";
	exit;
    }
#    print "Processing $file \n";
# Slurp all $file into $_;
    local $/=undef; open FILE,"<",$file or die "Cannot open $file\n"; local $_ = <FILE>; close FILE;
# Recursively call maudify on all loaded files (making sure that they have the right path)
#    print "Recursive maudification of the files included by $file \n";
    my @tokens = map(maudify(File::Spec->catfile((fileparse($file))[1],$_)), get_includes($_));
#    print "Back to $file. Tokens from its imported modules: @tokens\n";

    if ($file =~ /\.maude/) { return set(@tokens, get_tokens($_)); }

    print "Maudifying $file\n";

# Iterate and Maudify each included pattern
    s/($include)/
    {
	local $_ = $1;
	if    (m!^kmod!) { ($_,@tokens) = maudify_module($_,@tokens); }
	elsif (m!^(in|load)!) { s!\.kmaude\s*$!\.maude!s; }
	$_;
    }
    /gmse;

    my $maude_file = ($file =~ /^(.*)\.kmaude$/)[0].".maude";
    open FILE,">",$maude_file or die "Cannot write $maude_file\n"; print FILE $_; close FILE;

    return @tokens;
}


sub get_includes {
    local ($_) = @_;
    s/^---.*?$//gms;
    /^((?:\s*(?:in|load)\s+\S+)*)/s;
    return $1 =~ /^\s*(?:in|load)\s+(\S+)\s*$/gms;
}


sub maudify_module {
    (local $_, my @tokens) = @_;

#    print "Maudifying module \n$_\n with tokens @tokens";

# Step 1: Freeze all comments
    s!(---.*?(?=$))!freeze($1)!gme;

# Step 2: Freeze on-the-fly anonymous variable declarations
    s!_(:$ksort)!?$1!;
    s!(\?:$ksort)!freeze($1,"ANONYMOUS")!ge;

# Step 2: Declare the on-the-fly variables
    $_ = on_the_fly_kvars($_);

# Step 3: Reduce cell notation with _ to cell notation with ...
    s!<(\s*[^\s<]+\s*)_\s*>!<$1>... !gs;
    s!<\s*_(\s*/\s*[^\s>]+\s*)>! ...<$1>!gs;

# Step 4: Declare cell labels as operations
    $_ = add_cell_label_ops($_);

# Step 5: Add the module's newly defined tokens to @tokens
    @tokens = set(@tokens, get_tokens($_));

# Step 6: Add missing spaces around tokens
    $_ = spacify($_, @tokens);

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
    $_ = unfreeze($_);

    return ($_,@tokens);
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
		exit;
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
sub get_tokens {
    local $_ = shift;

# Builtin tokens
    my @builtinTokens = qw(=> = -> id: .K .List .Set .Bag .Map);

# Extracting all the defined operations
    my @ops=/\sops?\s+(.*?)\s+:\s+/gms;

# Put all operations in one string
    $_ = "@ops";

# Extract all tokens that appear in operations
    my @tokens = /$maude_special?($maude_unspecial+)/g;

# Add builtin tokens, remove duplicates, remove all tokens which are
# alphanumeric words (these are suppossed to be separated), then return
    return grep /\W/, set(@tokens,@builtinTokens);
}


# Next subroutine takes a string (usually comprising a kmaude file) and a list of tokens,
# and returns a string obtained from the original one by adding spaces to the left and/or
# to the right of tokens in the string
sub spacify {
    my ($lines,@tokens) = @_;
    my %substrings;

#    print "$lines\n@tokens\n";

# Put all tokens in a string
    my $tokenString = " @tokens ";
#    print "$tokenString\n";

# Make tokens into patterns
    map(s/([$special_perl_chars])/\\$1/g, @tokens);
#    print " @tokens \n";

# Compute a hash mapping each token to a list of pairs (before,after)
# Representing the contexts in which the token is a substring of other tokens
    foreach my $token (@tokens) {
#    print "\nToken $token ";
	my @pairs = ();
# Iterate through all matches of the token in the string of tokens
	while($tokenString =~ /$token/g) {
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
#	    print "$token : @pairs\n";
	    $substrings{$token} = \@pairs;
	}
    }

# Freeze all excluded substrings, which we do NOT want to be spacified
    $lines =~ s/($exclude)/freeze($1,"EXCLUDE")/gmse;

#    print "Iterating through maximal tokens\n";
    foreach my $token (@tokens) {
	if (! exists $substrings{$token})
	{
#	    print "$token\n";
	    $lines =~ s/(.)($token)(.)/add_spaces($1,freeze($2,"EXCLUDE"),$3)/gse;
	}
    }

    while (my ($token,$valref) = each %substrings) {
#	print "Token: $token: @$valref\n";
	my @temp = my @ba = @$valref;
	while ((my $before, my $after, @temp) = @temp) {
#	    print "$before!!!$after\n";
	    $lines =~ s/($before$token$after)/freeze($1,"TOKEN")/gse;
	}
	$lines =~ s/(.)($token)(.)/add_spaces($1,$2,$3)/gse;
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
    return "$marker".join("$specialSymbol",map(ord,(split('',$string))));

#    return "$specialSymbol$marker".join("$specialSymbol$marker",map(ord,(split('',$string))));
}

# Makes concrete all the frozen (sub)strings
sub unfreeze {
    my $all = shift;
    my $marker = "$default_freezer\b";
    if (@_) {
	$marker = shift;
    }

    $all =~ s/$marker(\d+(?:$specialSymbol\d+)*)/join("", map(chr, split("$specialSymbol",$1)))/gse;

#    $all =~ s/$specialSymbol$marker(\d+(?:$specialSymbol$marker\d+)*)/join("", map(chr, split("$specialSymbol$marker",$1)))/gse;

    return $all;
}

# Eliminates duplicates from a list, possibly reordering the remaining ones
sub set {
    my %hash = map { $_,1 } @_;
    return keys %hash;
}
