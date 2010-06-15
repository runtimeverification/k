#!/usr/bin/perl -w
use strict;
use File::Basename;
use File::Spec;
use Switch;

# next subroutine prints the usage message;
# $0 is initially bound to the program name, as typed
sub terminate {
    print "\nERROR: $_[0]\n\n" if defined $_[0];
    print "Usage:
  $0 (-option)* <source_file>[.kmaude|.maude] (-option)*

  This program takes a K language definition and translates
  it into a Maude executable specification.  The input K
  definition can be spread over several files and modules,
  all reachable from <source_file>[.kmaude|.maude], and the
  generated output will be saved in <source_file>-compiled.maude.

  <source_file> must be a K-Maude or a Maude file, expected
  to directly or indirectly (by loading other files) include
  the entire definition of the language.  It is highly
  recommended that one omits the (.maude or .kmaude) extension
  of the loaded files, to let this program choose the appropriate
  one depending upon the compilation stage or parameters.

  <source_file> is assumed to be a K-Maude file whenever it
  has the extension \".kmaude\" and a Maude file whenever
  it has the extension \".maude\".  If none of these extensions
  is provided, then the K-Maude file <source_file>.kmaude is
  considered if it exists; if <source_file>.kmaude does not exist,
  then the Maude file <source_file>.maude is considered instead.
  If none of the files <source_file>.kmaude or <source_file>.maude
  is found, then this program stops with an error message.

  The same name resolution principle as above is recursively
  applied on files directly or indirectly loaded by <source_file>.

  As part of the Maude-ification process, a corresponding
  file.maude file will be associated to each file.kmaude
  file directly or indirectly loaded by <source_file>.
  Note that these are only intermediate representation files,
  which are not executable.

  If an error occurs in the compilation process (including
  any Maude warnings), this program will stop, displaying the
  input, the (possibly partially) generated output, and the
  error/warning messages reported by Maude.  Files containing
  intermediate compilation results are also kept for debugging.

  Options
  -h (or -help) : print this message and exit
  -v (or -verbose) : verbose mode
  -m (or -maudify) : only maudify, do not kompile
  -c (or -compile) : only compile, do not maudify
  -l (or -lang or -language) <module_name> : start module

  The option -m generates all the Maude files file.maude
  corresponding to all the files file.kmaude reachable from
  <source_file>.  Note that Maude files are also allowed to
  load K-Maude files, which, as explained above, is the default
  choice whenever an extension is not given for the loaded file.
  This option is fast (since it does not compile the Maude-ified
  K language definition), so it is generally good for debugging.

  The option -c assumes that the K definition is already
  Maude-ified (either manually or using the above -m option).
  In particular, files with the extension .kmaude cannot be
  loaded anymore: the program terminates with an error if one
  attempts to do so, and the default extension is .maude.

  If the -l option is used, then <source_file> must
  contain a module called <module_name>.  If the option
  -l is not used, then <source_file> must include a module
  with the same root name, but capitalized.

  Technically, the command kompile lang.kmaude is equivalent to
  kompile -m lang.kmaude followed by kompile -c lang.maude.
  Since kompile -m lang.kmaude associates a corresponding .maude
  file to each reachable .kmaude file while it does not modify
  any of the reachable .maude files, in order for
  kompile -c lang.maude to work one is advised to not use
  extensions for the loaded file names.

  Examples

  kompile lang.kmaude : compiles the K language definition
  found in file lang.kmaude into an executable Maude
  specification saved in file lang-compiled.maude.
  The file lang.kmaude must contain a module named LANG.

  kompile lang3.kmaude -l LANG : compiles the K language
  definition reachable from module LANG of file lang3.kmaude
  into a Maude specification saved in file lang3-compiled.maude.

  kompile -v -m lang3.kmaude : it only (verbosely) Maude-ifies
  the K language definition reachable as above, saving it in
  file lang3.maude (and similarly for loaded files). To further
  compile the Maude-ified K definition, use the following:

  kompile lang3.maude -l LANG : it compiles the K definition
  starting with module LANG of file lang3.maude into an
  executable Maude specification saved in file
  lang3-compiled.maude.  lang3.maude is still allowed to load
  K-Maude files, which will be Maude-ified.

  kompile -l LANG lang3 -c : it compiles the already
  Maude-ified K definition starting with module LANG of file
  lang3.maude.  lang3.maude cannot load any K-Maude files; the
  default extension of loaded files is set to .maude.

" ;
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
my $maude_path = "maude";
my $maude_temp_file = "ERASE-ME-PLEASE";
my $maude_special = "[ $parentheses\\s_\\,\\`]";
my $maude_unspecial = "[^$parentheses\\s_\\,\\`]";
my $maude_backquoted = "(?:`\\(|`\\)|`\\{|`\\}|`\\[|`\\]|`\\,|_|[^$parentheses\\s\\,\\`])*";

#####
# K #
#####
# Pattern matched by K variables
my $kvar  = "[A-Za-z][A-Za-z0-9]*[']*";

# Pattern matched by K sorts
my $ksort = "[A-Z\\?\\!][A-Za-z0-9\\`\\+\\?\\!]*(?:\\{[A-Za-z0-9\\`\\+\\?\\!]*\\})?";

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
my $k_all_tools = File::Spec->catfile($k_tools_dir,"all-tools");
my $k_prelude = File::Spec->catfile(File::Spec->catfile($k_tools_dir,".."),"k-prelude");

my @kmaude_keywords = qw(context rule macro eq configuration op ops syntax kvar sort sorts subsort subsorts including kmod endkm);
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
my $maudify_only = 0;
my $compile_only = 0;
my $language_module_name = "";
my $language_file_name = "";

# File names for the input to be sent to the Maude compiler, as well as
# file names for the output, errors and temporary files generated by it
# These are useful for debugging
my $input_file  = "kompile_in.maude";
my $error_file  = "kompile_err.txt";
my $output_file = "kompile_out.txt";
my $temp_file   = "kompile_tmp.txt";

my $begin_compiled_module = "---K-MAUDE-GENERATED-OUTPUT-BEGIN---";
my $end_compiled_module   = "---K-MAUDE-GENERATED-OUTPUT-END---";

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
	terminate;
    }
    elsif (/^--?v(erbose)?$/) {
# By default, it is not verbose
	$verbose = 1;
    }
    elsif (/^--?m(audify)?$/) {
# By default, it maudifies and compiles
	$maudify_only = 1;
    }
    elsif (/^--?c(ompile)?$/) {
# By default, it maudifies and compiles
	$compile_only = 1;
    }
    elsif (/^--?l(ang|anguage)?$/) {
	$language_module_name = "?";
    }
    elsif (/^-/) {
	terminate("Unknown option $_");
    }
    else {
	$language_file_name = $_;
    }
}

# Check if an input file was given and exit if not
if ($language_file_name eq "") {
    terminate("No input file given");
}

# Check if both -m and -c are given together
if ($maudify_only && $compile_only) {
    terminate("Options -m and -c cannot be given together\n(-m/-c means \"only maudify/compile, do not compile/maudify\")");
}

# Check if the -c option is given together with a .kmaude file
if ($compile_only && $language_file_name =~ /.kmaude$/) {
    terminate("Option -c only works with a .maude file");
}

# Following is executed whenever the option -c was not selected
if (!$compile_only) {
# Maudify the .kmaude files reachable from file "$language_file_name"
    print_header("Maudifying $language_file_name") if $verbose;
    maudify_file("$language_file_name","");
#    print_header("Done with maudifying $language_file_name") if $verbose;
    print_header("Data resulting from maudifying $language_file_name") if $verbose;
    print "Sorts:\n------\n@all_sorts\n\n" if $verbose;
    print "Tokens:\n-------\n@all_tokens\n" if $verbose;
    $language_file_name =~ s/\.kmaude$//;
    print "\n" if $verbose;
}

# Following is executed whenever the option -m was not selected
if (!$maudify_only) {
# Remove .maude extension if there
    $language_file_name =~ s/\.maude$//;
    print_header("Compiling $language_file_name") if $verbose;
    compile();
    print "Compiled version written in $language_file_name-compiled.maude\n" if $verbose;
}


# Prints a visible message, like
# *************************
# *** Here is a message ***
# *************************
sub print_header {
    my $starred_line = my $text = "*** $_[0] ***";
    $starred_line =~ s/./*/g;
    print "\n$starred_line\n$text\n$starred_line\n\n";
}


# Next routine compiles the language definition in $language_file_name
# It also performs some sanity checks
sub compile {
# Assumes $language_file_name is a file name with no extension
# However, since we eventually call Maude on it, $language_file_name.maude must exist
    if (! -e "$language_file_name.maude") {
	terminate("File $language_file_name.maude does not exist");
    }

# Checking whether Maude is available
    run_maude("Detecting Maude ... ", "quit\n");

# Create the module name, if not already given, by capitalizing the file name
    if ($language_module_name eq "") {
	$language_module_name = uc($language_file_name);
    }

# File name where the compiled output will be stored:
    my $output_file_name = "$language_file_name-compiled.maude";

# Testing whether the input module $language_module_name exists
    run_maude("Testing if the input module $language_module_name exists ... ",
	      "load $language_file_name\n",
	      "show module $language_module_name .\n",
	      "quit\n");

# Compiling the input module $language_module_name
    $_ = run_maude("Compiling the definition ... ",
	      "load $language_file_name\n",
	      "load $k_all_tools\n",
	      "loop compile .\n",
	      "(compile $language_module_name .)\n",
	      "quit\n");
# If the keyword "Error" begins a line in the output, then extract and report the error message
    if (/^Error: (.*?)Bye/sm) {
	print "ERROR:\n";
	print $1;
	print "Aborting the compilation\n";
	exit(1);
    }
# If the output contains a generated Maude file, then write it in $output_file
    if (/$begin_compiled_module(.*?)$end_compiled_module/s) {
	open FILE,">",$output_file_name or die "Cannot create $output_file_name\n";
	print FILE "load $k_prelude\n";
	print FILE $1;
	close FILE;
    }
# Otherwise there must be some error that the script is now aware of, so show the whole thing
    else {
	print "Uncknown ERROR: cannot parse the output below (returned by the compiler)\n$_";
	print "Aborting the compilation\n";
	exit(1);
    }
}


# This is called whenever everything went fine, to clean up the temporary files
sub clean {
    unlink($input_file);
    unlink($output_file);
    unlink($error_file);
    unlink($temp_file);
}


# Running Maude (cross platform)
sub run_maude {
    my ($message,@commands) = @_;
    print $message if $verbose;
    open FILE,">",$input_file or die "Cannot create $input_file\n";
    print FILE "\n@commands\n";
    close FILE;
    system("$maude_path $input_file >$output_file 2>$error_file");
    if ($? == 0) {
	if (-s $error_file) {
	    print "ERROR:\n";
	    open FILE,"<",$error_file or die "Cannot open $error_file\n";
	    my $i = -1;
	    while (<FILE>) {
		++$i;
		if ($i < 10) {
		    print;
		}
		else {
		    last;
		}
	    }
	    if (<FILE>) {++$i;}
	    close FILE;
	    print "...\nCheck $error_file for the remaining errors\n" if $i==11;
	    print "Aborting the compilation\n";
	    exit(1);
	}
	print "DONE\n" if $verbose;
	local $/=undef;
	open FILE,"<",$output_file or die "Cannot open $output_file\n";
	local $_ = <FILE>;
	close FILE;
	clean();
	return $_;
    }
    else {
	print "\nMaude cannot be detected: the command $maude_path does not execute\n";
	print "Aborting the compilation\n";
	clean();
	exit(1);
    }
}


# The function maudify($file) does the following operations:
# 1) Maude-ifies $file in case it is a .kmaude file, generating a .maude file
# 2) It does the same recursively on each included file
# 3) Updates the global variables @all_sorts and @all_tokens
# - one to the list of sorts that are declared in the $file or in its included files
# - another to the list of tokens that appear in operations declared in the $file or its included files
sub maudify_file {
# Bind $file and $indent (the latter used for pretty printing when$verbose
    my ($file,$indent) = @_;
# If $file has extension .kmaude or .maude then tests if $file exists and errors if not
    if ($file =~ /\.k?maude$/) {
	if (! -e $file) {
	    terminate("File $file does not exist");
	}
    }
# If $file does not have the extension .kmaude or .maude the
    else {
# Add extension .kmaude if $file.kmaude exists
	if (-e "$file.kmaude") {
	    $file .= ".kmaude";
	}
# If not, then add extension .maude if $file.maude exists
	elsif (-e "$file.maude") {
	    $file .= ".maude";
	}
# Otherwise error: we only allow files with extensions .kmaude or .maude
	else {
	    terminate("Neither $file.kmaude nor $file.maude exist");
	}
    }

    print $indent."Processing file $file\n" if $verbose;
    $indent .= "|   ";
# Slurp all $file into $_;
    local $/=undef; open FILE,"<",$file or die "Cannot open $file\n"; local $_ = <FILE>; close FILE;

# Getting rid of comments, maintaining the line numbers of the remaining code
    s/($comment)/
    {
	local $_=$1;
	s!\S!!gs;
	$_;
    }/gsme;
    
    my $maudified = "";
    while (s/^(\s*)($top_level_pattern)(\s*)//sm) {
	(my $before, local $_, my $after) = ($1,$2,$3);
	if (m!^kmod\s+(\S+)!) {
	    print $indent."K module $1 ... " if $verbose;
	    $_ = maudify_module($_);
	    print "DONE\n" if $verbose;
	}
	elsif (m!^f?mod\s+(\S+)!) {
	    print $indent."Maude module $1 ... " if $verbose;
	    add_sorts($_);
	    add_tokens($_);
	    print "DONE\n" if $verbose;
	}
	elsif (m!^(?:in|load)\s+(\S+)!) {
	    maudify_file(File::Spec->catfile((fileparse($file))[1],$1),$indent);
	    s!\.kmaude\s*$!\.maude!s;
	}
	else {
#	    print "Top level pattern:\n$_\n" if $verbose;
	}
	$maudified = "$maudified$before$_$after";
    }
    
    if (/\S/) {
	print "ERROR: Cannot finish processing $file\n";
	print "ERROR: The following text does not parse:\n$_";
	exit(1);
    }
    
    $indent =~ s/\|   //;
    print $indent."Done with processing file $file\n" if $verbose;

    if ($file =~ /\.maude/) { return; }

    my $maude_file = ($file =~ /^(.*)\.kmaude$/)[0].".maude";
    open FILE,">",$maude_file or die "Cannot write $maude_file\n";
    print FILE $maudified;
    close FILE;
}


sub maudify_module {
    (local $_) = @_;

#    print "Maudifying module with tokens @all_tokens\n";

# Step: Add to @all_sorts all sorts defined a la Maude, with "sort(s)"
	add_sorts($_);

# Step: Freeze on-the-fly anonymous variable declarations
    s!_(:$ksort)!?$1!;
    s!(\?:$ksort)!freeze($1,"ANONYMOUS")!ge;

# Step: Desugar syntax N ::= Prod1 | Prod2 | ... | Prodn
# At the same time, also declare N as a sort if it is not declared already
	s!(syntax\s+.*?)(?=$kmaude_keywords_pattern)!make_ops($1)!gse;

# Step: Declare the on-the-fly variables
    $_ = on_the_fly_kvars($_);

# Step: Reduce cell notation with _ to cell notation with ...
    s!<(\s*[^\s<]+\s*)_\s*>!<$1>... !gs;
    s!<\s*_(\s*/\s*[^\s>]+\s*)>! ...<$1>!gs;

# Step: Declare cell labels as operations
    $_ = add_cell_label_ops($_);

# Step: Add the module's newly defined tokens to @tokens
    add_tokens($_);

# Step: Add missing spaces around tokens
    $_ = spacify($_);

# Step: Change .List into (.).List , etc.
    s!\.(K|List|Set|Bag|Map)([^\w\{])!(.).$1$2!gs;

# Step: Replace remaining _ by ? (spaces were put around _ by spacify)
    s! _ ! ? !gs;

# Step: Change K attributes to Maude metadata
    s!(\[[^\]]*\])!make_metadata($1)!gse;

# Step: Change K statements into Maude statements
    s!((?:$kmaude_keywords_pattern).*?)(?=(?:$kmaude_keywords_pattern|$))!k2maude($1)!gse;

# Step: Unfreeze everything still frozen
    $_ = unfreeze($_,"ANONYMOUS");
#    $_ = unfreeze($_);

    return $_;
}


# Takes a syntax statement and extracts sorts, subsorts and operations
sub make_ops {
	local ($_) = @_;
#	print "make_ops:\n$_\n";

# Grab the result sort and the productions, as well as all spacing
 	my ($spaces1,$result_sort,$spaces2,$productions,$spaces3) =  /^syntax(\s+)($ksort)(\s*)::=(.*?\S)(\s*)$/s;
#	print "\$productions\n$productions\n";

# Add $result_sort to @all_sorts if not already there
	my $sort_decl = "";
	if ( ! (grep { "$_" eq "$result_sort" } @all_sorts) ) {
	    $sort_decl = "sort $result_sort";
	    push(@all_sorts, $result_sort);
	}
	my $result = "$spaces1 $sort_decl $spaces2";

# Extract all productions in @productions
	my @productions = ($productions =~ /(.*?\S.*?(?:\s\|\s|$))/gs);

#        print "PRODS: ".join("#",@productions)."\n";

        foreach my $production (@productions) {
# Removing the | separator
		$production =~ s/(\s)\|(\s)/$1$2/gs;

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

# Replacing spaces in the production by "`"
		$production =~ s/\s+/`/gs;

# Removing unnecessary `
		$production =~ s/(^|$maude_special)`/$1/gs;
		$production =~ s/`($|$maude_special)/$1/gs;

		$result .= ($production eq "_")
					? "$space4 subsort @sorts < $result_sort$space5 "
					: "$space4 op $production : @sorts -> $result_sort$space5$attributes ";
        }

#print "Done\n";
	return "$result$spaces3";
}


sub op_attribute {
	local ($_) = @_;
	/strict|prec|gather|metadata|latex|ditto|format|assoc|comm|id:/;
}


sub k2maude {
    local ($_) = @_;
    s/macro(\s)/eq$1/gs;
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
#    my @ops = grep(split(/\s+/s, $_), /\sops?\s+(.*?)\s+:\s+/gms);
    my @ops = /\sops?\s+(.*?)\s+:\s+/gms;

# Put all operations in one string
    $_ = "@ops";

# Keep those operation names which have no _ or ` as tokens
    my @tokens = grep(!/[_`]/,split(/\s+/s));

# Extract all tokens that appear in operations
    @tokens = (@tokens, /$maude_special?($maude_unspecial+)/g) ;

# Add all meaningful tokens in @tokens to @all_tokens
    @all_tokens = set(@all_tokens, grep(/\W/, set(@tokens)));
}

# This subroutine returns a list of all spacifiable tokens that appear in operations defined (using op) in the argument
# By spacifiable tokens we mean ones that the tool may need to add spaces to their left and/or right
sub add_sorts {
    local $_ = shift;

# Extracting all the defined sorts
    my @sorts = /\ssorts?((?:\s+$ksort)+)\s+(?=\.|$kmaude_keywords_pattern)/gs;

#    print "\nSORTS: @sorts\n";

    @sorts = split(/\s+/, "@sorts");
	
#    print "Adding sorts: @sorts\nModule: $_\n" if $verbose;
# Add these sorts to @all_sorts
    @all_sorts = set(@all_sorts, @sorts);

# Add all sorts with alphanumerics to @all_tokens as well
    @all_tokens = set(@all_tokens, grep /\W/, @sorts);
}

# Next subroutine takes a string (most likely a kmaude module),
# and returns a string obtained from the original one by adding spaces to the left and/or
# to the right of tokens in the string; recall that the global @all_tokens holds all tokens
sub spacify {
    my ($lines) = @_;
    my @dag;
    my %index;     # holds index of each token
    my @array;     # holds token associated to each index
    my $i=0;

# First associate each token with a distinct number
    foreach my $token (@all_tokens) {
	$array[$i] = $token;
	$index{$token} = $i++;
    }

# Then create a dag as a an array of arrays over indexes
    for $i (0..$#array) {
	(my $token_pattern = $array[$i]) =~ s/([$special_perl_chars])/\\$1/g;
	$dag[$i] = [map($index{$_}, grep(/.$token_pattern|$token_pattern./, @all_tokens))];
    }

# Freeze all excluded substrings, which we do NOT want to be spacified
    $lines =~ s/($exclude)/freeze($1)/gmse;

# Spacify and then freeze each token in reversed topological order
# This way, we are sure that a subtoken of a token will never be spacified
    foreach my $token (map($array[$_], reverse(topological_sort(@dag)))) {
	(my $token_pattern = $token) =~ s/([$special_perl_chars])/\\$1/g;
	$lines =~ s/(.)($token_pattern)((?=.))/add_spaces($1,$2,$3)/gse;
    }
 
# Dirty hack: add spaces around anonymous variables, so that they will be properly
# translated into ? later on
    $lines =~ s/_/ _ /gs;

# Next unfreeze all tokens and return the spacified string
    return unfreeze($lines);
}


# Pass it as input a list of array references; these specify that that index into the
# list must come before all elements of its array.  Output is a topologically sorted
# list of indices, or undef if input contains a cycle.  Note that you must pass an array
# ref for every input elements (if necessary, by adding an empty list reference)! 
sub topological_sort {
    my @out = @_;
    my @ret;

# Compute initial in degrees
    my @ind;
    for my $l (@out) {
    ++$ind[$_] for (@$l)
    }

# Work queue
    my @q;
    @q = grep { ! $ind[$_] } 0..$#out;

# Loop
    while (@q) {
	my $el = pop @q;
	$ret[@ret] = $el;
	for (@{$out[$el]}) {
	    push @q, $_ if (! --$ind[$_]);
	}
    }

    return @ret == @out ? @ret : undef;
}


# Adds spaces before and/or after token, if needed
sub add_spaces {
    my ($before,$token,$after) = @_;
    if ($before =~ /\w$/ && $token =~ /^\w/) { return "$before$token"; }
    if ($after =~ /^\w/ && $token =~ /\w$/) { return "$before$token"; }
    return ($before.(($before =~ /$maude_special/) ? "":" ").freeze($token).(($after =~ /$maude_special/) ? "":" "));
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
