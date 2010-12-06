#!/usr/bin/perl -w
use strict;
use File::Basename;
use File::Spec;
use Switch;
use Cwd; 
use Cwd 'abs_path';
my $path = File::Spec->catfile((File::Basename::fileparse($0))[1], 'common_functions.pl');

require $path;
my $verbose = 0;
my $help = 0;

# next subroutine prints the usage message;
# $0 is initially bound to the program name, as typed
sub terminate {
    print "\nERROR: $_[0]\n\n" if defined $_[0];
    print "Usage: 
  $0 (-option)* <source_file>[.k|.kmaude|.maude] (-option)*

  Options
  -h (or -help) : print this message and exit
  -v (or -verbose) : verbose mode
  -m (or -maudify) : only maudify, do not kompile
  -c (or -compile) : only compile, do not maudify
  -l (or -lang or -language) <module_name> : start module
  -file : the input source file (optional)
  -nd : compile for full non-determinism in heating/cooling
  -flat : slurp all k or kmaude files into one k file 
  -u (or -unquote) : unquote the maude meta-terms to increase speed
  -latex : maudifies/compiles for generating latex output
  -pdf : maudifies/compiles for generating pdf output
  -ps : maudifies/compiles for generating ps output
  -eps : maudifies/compiles for generating eps output
  -png : maudifies/compiles for generating png output
  -crop : maudifies/compiles for generating a nice crop-pdf output
     -style : useful for typesetting (optional)
  \n" if (!$verbose && !$help);

    print "Usage:
  $0 (-option)* <source_file>[.k|.kmaude|.maude] (-option)*
  
  This program takes a K language definition and translates
  it into a Maude executable specification.  The input K
  definition can be spread over several files and modules,
  all reachable from <source_file>[.k|.kmaude|.maude], and the
  generated output will be saved in <source_file>-compiled.maude.

  <source_file> must be a K-Maude or a Maude file, expected
  to directly or indirectly (by loading other files) include
  the entire definition of the language.  It is highly
  recommended that one omits the (.maude or .kmaude or .k) extension
  of the loaded files, to let this program choose the appropriate
  one depending upon the compilation stage or parameters.

  <source_file> is assumed to be a K-Maude file whenever it
  has the extension \".kmaude\" or \".k\" and a Maude file whenever
  it has the extension \".maude\".  If none of these extensions
  is provided, then the K-Maude file <source_file>.kmaude (or 
  <source_file>.k) is  considered if it exists; if <source_file>.kmaude 
  (or <source_file>.k) does not exist, then the Maude file 
  <source_file>.maude is considered instead.
  If none of the files <source_file>.kmaude (<source_file>.k) or 
  <source_file>.maude is found, then this program stops with an error message.

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
  -file : the input source file (optional)
  -nd : compile for full non-determinism in heating/cooling
  -flat : slurp all k or kmaude files into one k file 
  -u (or -unquote) : unquote the maude meta-terms to increase speed
  -latex : maudifies/compiles for generating latex output
  -pdf : maudifies/compiles for generating pdf output
  -ps : maudifies/compiles for generating ps output
  -eps : maudifies/compiles for generating eps output
  -png : maudifies/compiles for generating png output
  -crop : maudifies/compiles for generating a nice crop-pdf output
    -style : useful for typesetting (optional)

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

  Technically, the command \"kompile lang.kmaude\" is equivalent to
  \"kompile -m lang.kmaude\" followed by \"kompile -c lang.maude\".
  Since \"kompile -m lang.kmaude\" associates a corresponding .maude
  file to each reachable .kmaude file while it does not modify
  any of the reachable .maude files, in order for
  \"kompile -c lang.maude\" to work one is advised to not use
  extensions for the loaded file names; in other words, write, e.g.,
  \"in/load lang-syntax\" instead of \"in/load lang-syntax.kmaude\".

  The option -latex is used for typesetting a K definition.  It can
  be used in combination with any of the other options above.  If
  used with -m, then it only maudifies the (entire) given input file,
  adding for each operation a special latex attribute inside the
  operation's metadata.  If used with -c, it assumes that the input
  file is already maudified as above and generates a latex and a
  PDF file corresponding to a list of specified module names.  The list
  of module names should be given following the -latex option.  If used
  wihout any of -m or -c, it first applies the -m and then the -c, as
  explained in the paragraph above but with the additional option -latex.

  The optional parameter passed to -style (which only makes sense when
  the -latex option is used) can alter the style used for typesetting.
  Currently, there are two style options available, bb, for typesetting
  via tikz graphical cells, and mm, for typesetting using the simple
  mathematical notation.  The default option is bb.

  If a file <source_file>.sty is provided by the user in the current
  directory, it will be included in the generated latex file after the
  above mentioned style, and thus could be used to alter the default
  typesetting macros.
 
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

  kompile -latex LANG LANG-SEMANTICS LANG-SYNTAX -f lang3
  or
  kompile lang3 -latex LANG LANG-SEMANTICS LANG-SYNTAX
  It typsets the specified modules reachable from the input
  file lang3.
  
  The -pdf, -png, -ps, -eps and -crop options can be used in 
  the same way the -latex option is used in the example above.
  
" if ($verbose || $help); 
    print "\nERROR: $_[0]\n\n" if defined $_[0];
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

#########
# Latex #
#########
#my $latex_special = "[\\#\\$\\{\\}\\[\\]\\&\\^\\_\\%\\~\\\\]";
my $latex_special = '[\\#\\$\\{\\}\\[\\]\\&\\^\\_\\%\\~\\\\]';

#####
# K #
#####
# Pattern matched by K variables
my $kvar  = "[A-Za-z][A-Za-z0-9]*[']*";

# Pattern matched by K sorts
my $ksort = "[A-Z][A-Za-z0-9\\`\\+\\?\\!]*(?:\\{[A-Z][A-Za-z0-9\\`\\+\\?\\!]*\\})?";
# TODO: test exhaustively :-)

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
my $k_to_latex = File::Spec->catfile($k_tools_dir,"k-to-latex");
my $k_prelude = File::Spec->catfile(File::Spec->catfile($k_tools_dir,".."),"k-prelude");
my $k_nice_pdf = File::Spec->catfile($k_tools_dir, "nice-pdf.sh");

my @kmaude_keywords = qw(context rule macro eq ceq configuration op ops syntax kvar sort sorts subsort subsorts including kmod endkm);
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
		"(?:in|load|require)\\s+\\S+"
));

# Configuration pattern: excludes, for the spacing, from the above all those substrings matching $exclude
my $exclude = join("|",
		   "\^\\s*(?:in|load|require)\\s+\\S+\\s*\$",               # in/load of a file
		   "kmod\\s+(?:\\S*(?=\\s))",                               # kmodule name
		   "including(?:.*?(?=\\s+(?=$kmaude_keywords_pattern)))",  # included module expressions
		   ":$ksort",                                               # sort declarations for other than ordinary $kvar
		   "ops?\\s+.*?(?=\\s+(?=$kmaude_keywords_pattern))",       # operation declarations
		   "$klabel",                                               # K labels
		   "rule\\s*\\[[^\\[\\]]*\\]\\s*:",                         # rule labels
		   "\\d+\\.\\d+",                                           # real numbers
		   "-\\d+"                                                  # negative integer
		   );

my $modules_list = "[A-Z\\-\\s]+[A-Z]";
# my $modules_list = "[a-zA-Z\\-\\+]+(?:\\-(latex|pdf|crop|ps|eps|png|h|v|m|c|l|file|nd|flat|u|style))";

# @all_sorts will hold all defined sorts
my @all_sorts = ();

# @all_tokens will hold all defined tokens
my @all_tokens = @builtin_tokens;

my $style = "bb";
my $maudify_only = 0;
my $compile_only = 0;
my $language_module_name = "";
my $language_file_name = "";
my $lang_name = "";
my $unquote = 0;
my $flat = 0;

# latex, pdf, eps, ps, png, crop
my $pdf = 0;
my $latex = 0;
my $eps = 0;
my $ps = 0;
my $png = 0;
my $crop = 0;

# used for generating modules for KLabels
my $klabels = "";

# File names for the input to be sent to the Maude compiler, as well as
# file names for the output, errors and temporary files generated by it
# These are useful for debugging
# my $input_file  = "kompile_in.maude";
# my $error_file  = "kompile_err.txt";
# my $output_file = "kompile_out.txt";
# my $temp_file   = "kompile_tmp.txt";
my $input_file  = fresh("kompile_in", ".maude");
my $error_file  = fresh("kompile_err", ".txt");
my $output_file = fresh("kompile_out", ".txt");
my $temp_file   = fresh("kompile_tmp", ".txt");
my $kshared = File::Spec->rel2abs(File::Spec->catfile(File::Spec->curdir(), "shared.maude"));
my $mset = 0;

my $begin_compiled_module = "---K-MAUDE-GENERATED-OUTPUT-BEGIN---";
my $end_compiled_module   = "---K-MAUDE-GENERATED-OUTPUT-END---";

#########################
# </TOOL CONFIGURATION> #
#########################

my @kmodules = ();

my @newcommands = ();
my $newcommand_prefix = "ksyntax";
my $newcommand_counter = 0;
my $newcommand_base = 6;

# modules to be 
my @latexify_modules =();
my @pdf_modules = ();
my @ps_modules = ();
my @eps_modules = ();
my @png_modules = ();
my @crop_modules = ();

# clean the old temporary files
erase_temp();

# Process the command arguments
foreach (@ARGV) {
    if (($language_file_name eq "?") && !/^-/) {
	$language_file_name = $_;
    }
    elsif (($language_module_name eq "?") && !/^-/) {
	$language_module_name = $_;
    }
    elsif (($style eq "?") && !/^-/) {
	$style = $_;
    }
    elsif (/^--?h(elp)?$/) {
# Terminates with usage info when asked for help
	$help = 1;
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
    elsif (/^--?file$/) {
	$language_file_name = "?";
    }
    elsif (/^--?nd$/) {
       $k_all_tools .= "-nd";
    }
    elsif (/^--?flat$/) {
	$flat = 1;
    }
    elsif (/^--?latex$/) {
	$latex = 1;
    }
    elsif (/^--?pdf$/) {
	$pdf = 1;
    }
    elsif (/^--?ps$/) {
	$ps = 1;
    }
    elsif (/^--?eps$/) {
	$eps = 1;
    }
    elsif (/^--?png$/) {
	$png = 1;
    }
    elsif (/^--?crop$/) {
	$crop = 1;
    }
    elsif (/^--?style$/) {
	$style = "?";
    }
    elsif (/^--?u(nquote)?$/)
    {
	$unquote = 1;
    }
    elsif (/^-/) {
	terminate("Unknown option $_");
    }
    elsif (($latex || $pdf || $ps || $eps || $png || $crop) && /[A-Z\-]+/)
    {
	# do nothing
#	print "MODULES: $_\n";
    }
    else {
	$language_file_name = $_;
    }
}


# Extract only language name without path
$lang_name = basename($language_file_name);
$lang_name =~ s/\..*?$//;

# print "MODULES:\n   PDF $pdf\n   LATEX $latex\n   PS: $ps\n   EPS: $eps\n   PNG: $png\n   CROP: $crop\n\n";

my $args = "@ARGV";
# print "ARGS: $args\n";

# get latex modules
if ($args =~ /--?latex\s+($modules_list)/)
{
    @latexify_modules = split(/\s+/, $1);
#    print "LATEX M: |@latexify_modules|\n"; 
}

# get pdf modules
if ($args =~ /--?pdf\s+($modules_list)/)
{
    @pdf_modules = split(/\s+/, $1);
#    print "PDF M: |@pdf_modules|\n"; 
}

# get ps modules
if ($args =~ /--?ps\s+($modules_list)/)
{
    @ps_modules = split(/\s+/, $1);
    # print "PS M: |@ps_modules|\n"; 
}

# get eps modules
if ($args =~ /--?eps\s+($modules_list)/)
{
    @eps_modules = split(/\s+/, $1);
#    print "EPS M: |@eps_modules|\n"; 
}

# get png modules
if ($args =~ /--?png\s+($modules_list)/)
{
    @png_modules = split(/\s+/, $1);
#    print "PNG M: |@png_modules|\n"; 
}

# get crop modules
if ($args =~ /--?crop\s+($modules_list)/)
{
    @crop_modules = split(/\s+/, $1);
#    print "CROP M: |@crop_modules|\n"; 
}

# Check if an input file was given and exit if not
if ($language_file_name eq "") {
    terminate("No input file given");
}

# Check if both -m and -c are given together
if ($maudify_only && $compile_only) {
    terminate("Options -m and -c cannot be given together\n(-m/-c means \"only maudify/compile, do not compile/maudify\")");
}

# Check if the -c option is given together with a .k or .kmaude file
if ($compile_only && $language_file_name =~ /(?:.k|.kmaude)$/) {
    terminate("Option -c only works with a .maude file");
}

# Check that a $language_file_name was indeed given if -f option was used
if ($language_file_name eq "?") {
    terminate("Option -f|-file requires that a file name be given right after");
}

# Check that a $language_module_name was indeed given if -l option was used
if ($language_module_name eq "?") {
    terminate("Option -l|-lang|-language requires that a module name be given right after");
}

# Check that a $style was indeed given if -style option was used
if ($style eq "?") {
    terminate("Option -style requires that a style be given right after");
}

# Check that at least one module name was given with -latex option
if ($latex == 1 && !@latexify_modules) {
    terminate("At least one module name must be given right after -latex");
}

# Check that at least one module name was given with -pdf option
if ($pdf == 1 && !@pdf_modules) {
    terminate("At least one module name must be given right after -pdf");
}

# Check that at least one module name was given with -ps option
if ($ps == 1 && !@ps_modules) {
    terminate("At least one module name must be given right after -ps");
}

# Check that at least one module name was given with -eps option
if ($eps == 1 && !@eps_modules) {
    terminate("At least one module name must be given right after -eps");
}

# Check that at least one module name was given with -png option
if ($png == 1 && !@png_modules) {
    terminate("At least one module name must be given right after -png");
}

# Check that at least one module name was given with -crop option
if ($crop == 1 && !@crop_modules) {
    terminate("At least one module name must be given right after -crop");
}
# Create the module name, if not already given, by capitalizing the file name
    if ($language_module_name eq "") {
	$language_module_name = uc($language_file_name);
	$language_module_name =~ s/\.K$|\.KMAUDE$|\.MAUDE$|\.M$//;
    }

# Check the file for syntax errors
    setVerbose() if $verbose;
    syntax_common_check($language_file_name);
    
# build inclusion trees
    appendFileInTree("$language_file_name", "");
    recurseIntoFiles($language_file_name);

# flatten if $flat is set
if ($flat)
{
	flattening($language_file_name);
	exit(0);
}

# Following is executed whenever the option -c was not selected
if (!$compile_only) {
# Maudify the .k|.kmaude files reachable from file "$language_file_name"
    print_header("Maudifying $language_file_name") if $verbose;

    # maudify
    maudify_file("$language_file_name","");
#    print "Maudification: $language_file_name\n\n";
    
    if ($klabels ne "")
    {
	
	my @tmp = split(/\s+/, $klabels);
	@tmp = uniq(@tmp);
	my $tmp = "ops @tmp : -> KLabel [metadata \"generated label\"] . ";
	my $dir = cwd;
	open FILE,">",$kshared or die "Cannot create $kshared\n";
	my $kprelude = abs_path($k_prelude);
	print FILE "in $kprelude\nmod K-SHARED is including K . \n\t$tmp\nendm";
	close FILE;
	
	my $filess = getFileList();
	if ($filess ne "")
	{
	    my @files = split(/\s+/, $filess);
	    foreach my $f(@files)
	    {
		$f =~ s/\.k$/\.maude/s;
		my $maudified = get_file_content($f);
#		print "F: $f\nM: $maudified\n\n";
		$maudified =~ s/(in|load)[\s\.\/]*k-prelude/in $kshared/;
		open FILE,">",$f or die "Cannot open $f\n";
		print FILE $maudified;
		close FILE;
	    }
	}
	    
    }
    

    
#    print_header("Done with maudifying $language_file_name") if $verbose;
    print_header("Data resulting from maudifying $language_file_name") if $verbose;
    print "Sorts:\n------\n@all_sorts\n\n" if $verbose;
    print "Tokens:\n-------\n@all_tokens\n" if $verbose;
    $language_file_name =~ s/(\.k|\.kmaude)$//;
    print "\n" if $verbose;

    print_header("New commands that will be added to the generated latex file") if $verbose && ($latex || $pdf || $crop || $ps || $eps || $png);
    print join("\n",@newcommands)."\n" if $verbose && ($latex || $pdf || $crop || $ps || $eps || $png);
}

# Following is executed whenever the option -m was not selected
if (!$maudify_only) {

# Remove .maude extension if there
    $language_file_name =~ s/\.maude$//;

# Since we eventually call Maude on $language_file_name, $language_file_name.maude must exist
    if (! -e "$language_file_name.maude") {
	terminate("File $language_file_name.maude does not exist");
    }

# Checking whether Maude is available
    run_maude("Detecting Maude ... ", "quit\n");

# Calling either the maude compiler or the latex/pdf compiler, depending upon $latex/$pdf
    if ($latex || $pdf || $ps || $eps || $png || $crop) 
    {
	make_latexify() if $latex;
	make_pdf() if $pdf;
	make_eps() if $eps;
	make_ps() if $ps;
	make_png() if $png;
	make_crop() if $crop;
    }
    else {
	compile();
    }
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


sub latexify {
    
    my ($format, @modules) = @_;
  
    foreach(@modules)
    {
	if (!exist($_))
	  {
	      print "Module $_ doesn't exist in your defintion.\n" if emptyModuleList();
	      exit(1) if emptyModuleList();
	  }
    }
    
# Assumes $language_file_name is a file name with no extension

    print_header("Generate $format version for module $language_module_name from language definition $language_file_name") if $verbose;

# 
    $_ = run_maude("Getting modules META-MODULE and K-TECHNIQUE ... ",
		   "load $k_prelude\n",
		   "show module META-MODULE .\n",
		   "show module K-TECHNIQUE .\n",
		   "quit\n");
    
    s/^Bye.//gms;
    s/(\[[^\[\]]*?)comm([^\[\]]*?\])/$1$2/gms;

    open FILE,">",$temp_file or die "Cannot create $temp_file\n";
    print FILE;
    close FILE;
    print "Temporary modules META-MODULE and K-TECHNIQUE written in $temp_file\n" if $verbose;

    my $latex_output = $_ =
	run_maude("Calling the Maude Latex-ifier ... ",
		  "load $language_file_name\n",
		  "set show advisories off .\n",
		  "load $temp_file\n",
		  "select META-LEVEL .\n",
		  "select $language_module_name .\n",
		  "set show advisories on .\n",
		  "load $k_to_latex\n",
		  "set print attribute on .\n",
		  "loop latex-print .\n",
		  map("(print $_ .)\n", @modules),
#		  "(print $language_module_name .)\n",
		  "quit\n");

    s/\\begin{module}.*?\\end{module}//gms;
    my @l_modules = ($latex_output =~ /(\\begin{module}.*?\\end{module})/gms);
    if (@l_modules && !/\\begin{module}/) {
	print "Latex style used: $style\n" if $verbose;
	

# File name where the compiled output will be stored:
	my $output_file_name = "$lang_name-$format.tex";
	open FILE,">",$output_file_name or die "Cannot create $output_file_name\n";
	print FILE "\\documentclass{article}\n";
	print FILE "\\usepackage{import}\n";
	print FILE "\\import{$k_tools_dir}{k2latex.$style.sty}\n";
        if (-e "$language_file_name.sty") {
	   print FILE "\\input{$language_file_name.sty}\n";
        }
	print FILE join("\n",@newcommands)."\n";
	print FILE "\\begin{document}\n";
	print FILE join("\\newpage", @l_modules)."\n";
	print FILE "\\end{document}\n";
	close FILE;
	print "Latex version written in $output_file_name\n" if $verbose;
    }
    else {
	print "ERROR: \\begin{module} ... \\end{module} not found in generated output\n";
	print "This error most likely due to wrong latex attributes\n";
	print "Check generated output in $output_file\n";
	open FILE,">",$output_file or die "Cannot create $output_file\n";
	print FILE $latex_output;
	close FILE;
	print "Aborting the compilation\n";
	exit(1);
    }
}

# run latex
sub run_latex
{
    my $tex_file = shift;
    
    # get approx pdf file
    my $latex_out = get_file_content("$tex_file.tex");
    $latex_out =~ s/^\\documentclass\[landscape\]/\\documentclass/;
    $latex_out =~ s/\\begin{document}/\\geometry{papersize={1400mm,11in},textwidth=1380mm}\\pagestyle{empty}\\begin{document}/;
    $latex_out =~ s/\\newpage/\\bigskip/g;
    # print $latex_out;
    
    open FILE,">", "$tex_file-temp.tex" or die "Cannot create $tex_file-temp.tex\n";
    print FILE $latex_out;
    close FILE;

    # create pdf
    my $status = system("latex -interaction=nonstopmode $tex_file-temp.tex > out");
    if (($status >>= 8) != 0)
    {
	throw_error("Failed to run latex. Exit status $status.\n");
    }
    # get number of pages
    my $pages = 0;
    
    # latex acts weird.. it generates all the temp files in the same directory 
    # but the tex file in other directory
    # $tex_file =~ s/\.\.\///g;
    
    my $log = get_file_content("$tex_file-temp.log");
#    my $log = get_file_content("$lang_name-temp.log");
    if ($log =~ /(\d+)\s+pages?/)
    {
	$pages = $1;
    }
#    print "PAGES: $pages\n";

    unlink("out");
    unlink("$tex_file-temp.aux");    
    unlink("$tex_file-temp.log");    
    unlink("$tex_file-temp.dvi");    
    unlink("$tex_file-temp.tex");    
    return $pages;
}

sub get_file_content
{
    my $filename = shift;
    
    open FILE, "<", $filename or die "Could not open $filename:\n$!";
    my @input = <FILE>;
    close FILE;
    
    return "@input";
}

# generates latex if $latex
sub make_latexify
{
    latexify("latex", @latexify_modules);
    rename("$lang_name-latex.tex", "$lang_name.tex");
    print "Generated $lang_name.tex which contains modules: @latexify_modules\n";
}

sub get_pdf_crop
{
    
    my ($format, @modules) = @_;

    latexify("$format", @modules);

    # modify page and save it
    my $latex_out = get_file_content("$lang_name-$format.tex");

    # Find number of pages
    my $pages = run_latex("$lang_name-$format");
    my $h = 9 * $pages;
    my $ph = $h + 1;
    $latex_out =~ s/^\\documentclass\[landscape\]/\\documentclass/;
    my $settings = "\\geometry{papersize={1400mm,".$ph."in},textheight=".$h."in,textwidth=1380mm}\\pagestyle{empty}\\begin{document}\\noindent\\hspace{-2px}\\rule{1px}{1px}";
    $latex_out =~ s/\\begin{document}/$settings/;
    $latex_out =~ s/\\newpage/\\bigskip/g;

    open FILE,">", "$lang_name-$format.tex" or die "Cannot create $lang_name-$format.tex\n";
    print FILE $latex_out;
    close FILE;

    # Generate pdf
    my $status = system("latex -output-format=pdf -interaction=nonstopmode $lang_name-$format.tex> out");
    # print "Failed to run latex. Exit status $status.\n" if (($status >>= 8) != 0);
    throw_error("Failed to run latex. Exit status $status.\n") if (($status >>= 8) != 0);
   
    
   # Generate pdf crop
    $status = system("pdfcrop $lang_name-$format.pdf > out");
    throw_error("Failed to generate crop version for pdf. Exit status $status.\n") if (($status >>= 8) != 0);
    
    rename("$lang_name-$format-crop.pdf", "$lang_name-$format.pdf");

    unlink("$lang_name-$format.aux") if !$verbose;
    unlink("$lang_name-$format.log") if !$verbose;
    unlink("$lang_name-$format.tex") if !$verbose;
    unlink("out");
}

# generates pdf if $pdf
sub make_pdf 
{
    # Generate eps
    get_pdf_crop("pdf", @pdf_modules);
    rename("$lang_name-pdf.pdf", "$lang_name.pdf");
    print "Generated $lang_name.pdf which contains modules: @pdf_modules\n";
}

# generate ps if $ps
sub make_ps
{
    get_pdf_crop("ps", @ps_modules);

    # Generate ps
    my $status = system("pdf2ps $lang_name-ps.pdf 2>/dev/null");
    throw_error("Failed to generate ps. Exit status $status.\n") if (($status >>= 8) != 0);
    
    # rename ps file
    rename("$lang_name-ps.ps", "$lang_name.ps");
    print "Generated $lang_name.ps which contains modules: @ps_modules\n";
    
    # delete auxialiary files if not verbose
    unlink("$lang_name-ps.pdf") if !$verbose;
}

sub make_eps
{
    get_pdf_crop("eps", @eps_modules);

    # Generate ps
    my $status = system("pdf2ps $lang_name-eps.pdf 2>/dev/null");
    throw_error("Failed to generate ps temporary file for generating eps. Exit status $status.\n") if (($status >>= 8) != 0);

    # Generate eps
    $status = system("ps2eps $lang_name-eps.ps 2>/dev/null");
    throw_error("Failed to generate eps. Exit status $status.\n") if (($status >>= 8) != 0);
    
    # rename eps file
    rename("$lang_name-eps.eps", "$lang_name.eps");
    print "Generated $lang_name.eps which contains modules: @eps_modules\n";

    unlink("$lang_name-eps.pdf") if !$verbose;
    unlink("$lang_name-eps.ps") if !$verbose;
}

sub make_png
{
    get_pdf_crop("png", @png_modules);

    # Generate png
    my $status = system("gs -q -dNOPAUSE -sDEVICE=pngalpha -dBATCH -dEPSCrop -r150 -sOutputFile=$lang_name-png.png $lang_name-png.pdf");
    throw_error("Failed to generate png. Exit status $status.\n") if (($status >>= 8) != 0);

    # rename png file
    rename("$lang_name-png.png", "$lang_name.png");
    print "Generated $lang_name.png which contains modules: @png_modules\n";

    # delete auxialiary files if not verbose
    unlink("$lang_name-png.eps") if !$verbose;
    unlink("$lang_name-png.pdf") if !$verbose;
}

# generates a nice - pdf if $crop
sub make_crop
{
    latexify("crop", @crop_modules);

    # modify page and save it
    my $latex_out = get_file_content("$lang_name-crop.tex");

    # Find number of pages
    my $pages = run_latex("$lang_name-crop");
    my $h = 9 * $pages;
    my $ph = $h + 1;
    $latex_out =~ s/^\\documentclass\[landscape\]/\\documentclass/;
    my $settings = "\\geometry{papersize={1400mm,".$ph."in},textheight=".$h."in,textwidth=1380mm}\\pagestyle{empty}\\begin{document}\\noindent\\hspace{-2px}\\rule{1px}{1px}";
    $latex_out =~ s/\\begin{document}/$settings/;
    
    # initial settings
    open FILE,">", "$lang_name-crop.tex" or die "Cannot create $lang_name-crop.tex\n";
    print FILE $latex_out;
    close FILE;    

    # Generate pdf
    my $status = system("latex -output-format=pdf $lang_name-crop.tex > out");
    throw_error("Failed to run latex. Exit status $status.\n") if (($status >>= 8) != 0);
    
    # Generate pdf-crop
    $status = system("pdfcrop $lang_name-crop.pdf > out");
    throw_error("Failed to generate crop pdf. Exit status $status.\n") if (($status >>= 8) != 0);

    # print message
    rename("$lang_name-crop-crop.pdf", "$lang_name-crop.pdf");
    print "Generated $lang_name-crop.pdf which contains modules: @crop_modules\n";
    
    # delete auxialiary files if not verbose
    unlink("$lang_name-crop.tex") if !$verbose;
    unlink("$lang_name-crop.aux") if !$verbose;
    unlink("$lang_name-crop.dvi") if !$verbose;
    unlink("$lang_name-crop.log") if !$verbose;
    unlink("$lang_name-crop.tex") if !$verbose;
    unlink("out");
    
}


# Next routine compiles the language definition in $language_file_name
# It also performs some sanity checks
sub compile {
# Assumes $language_file_name is a file name with no extension
    
    # add missing subsortations
    add_subsorts();
    
#    exit(1);
# Testing whether the input module $language_module_name exists
    run_maude("Testing if the input module $language_module_name exists ... ",
	      "load $language_file_name\n",
	      "show module $language_module_name .\n",
	      "quit\n");

    print_header("Compiling $language_file_name, starting with module $language_module_name") if $verbose;

# File name where the compiled output will be stored:
    my $output_file_name = "$language_file_name-compiled.maude";

# # Compiling the input module $language_module_name
    if ($unquote)
    {
	# If unquote is set then do some changes
	$_ = run_maude("Compiling the definition ... ",
	    "load $language_file_name\n",
	    "load $k_all_tools\n",
	    # "loop compile .\n",
	    # "(compile $language_module_name .)\n",
	    "set print attribute off .\n",
	    "rew compile('$language_module_name) .\n",
	    "quit\n");
	
	my @lines = split(/\n/, $_);
	shift @lines;
	shift @lines;
	shift @lines;
	pop @lines;
	my $errorSet = 0;
	if ($lines[0] =~ s/result \[ModuleSet\]: (.*)$/$1/)
	{
	    $errorSet = 1;
	}
	$lines[0] =~ s/^result SModule: (.*)$/$1/;
	$_ = join("\n", @lines);
	$_ = unquote($_);
	if ($errorSet)
	{
	    print "ERROR:\n";
	    
	    # fix tokens
	    $_ =~ s/\(/\(/g;
	    $_ =~ s/\)/\)/g;
	    $_ =~ s/\{/\{/g;
	    $_ =~ s/\}/\}/g;
	    $_ =~ s/\,/\,/g;
	    
	    # fix spaces
	    $_ =~ s/ \{ /\{/g;
	    $_ =~ s/ \} /\}/g;
	    $_ =~ s/ \( /\(/g;
	    $_ =~ s/ \) /\)/g;
	    $_ =~ s/ \, /\, /g;
	    print $_;
	    print "Aborting the compilation\n";
	    exit(1);
	}
	$_ = "$begin_compiled_module$_$end_compiled_module";
    }
    else
    {
	$_ = run_maude("Compiling the definition ... ",
	    "load $language_file_name\n",
	    "load $k_all_tools\n",
            "---(\n",
            "red in COMPILE-ONESHOT : partialCompile(upModule('$language_module_name , false),'???) .\n",
            "quit\n",
            "---)\n",
	    "loop compile .\n",
	    "(compile $language_module_name .)\n",
	    "quit\n");	
    }

# If the keyword "Error" begins a line in the output, then extract and report the error message
    if (/^Error: (.*?)Bye/sm) {
	print "ERROR:\n";
	print $1;
	print "Aborting the compilation\n";
	exit(1);
    }

# If the output contains a generated Maude file, then write it in $output_file_name
    if (/$begin_compiled_module(.*?)$end_compiled_module/s) {
	open FILE,">",$output_file_name or die "Cannot create $output_file_name\n";
	print FILE "load $k_prelude\n";
	print FILE $1;
	close FILE;
	print "Compiled version written in $output_file_name\n" if $verbose;
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

    # call maude
    my $status = system("$maude_path -no-banner -no-wrap $input_file >$output_file 2>$error_file");
    if (($status >>= 8) != 0)
    {
	my $err = get_file_content($error_file);
	$err =~ s/\n.*?$//sg;
	print "$err\nFailed to run maude.\nExit status $status.\n" ;
	exit(1);
    }

    if ($? == 0) {
	if (-s $error_file) {
	    open FILE,"<",$error_file or die "Cannot open $error_file\n";
	    print "ERROR:\n";
	    my $i = -1;
	    while (<FILE>) {
		++$i;
		my $err_msg = "";
		my $size = 180;
		$err_msg = "... (check $error_file to find the complete error)\n" if length($_) > $size;
		if ($i < 10) {
		    print substr($_, 0, $size) . $err_msg;
		}
		else {
		    $_ = substr($_, 0, $size) . $err_msg;
		    last;
		}
	    }
	    if (<FILE>) {++$i;}
	    close FILE;
	    print "...\nCheck $error_file for the remaining errors\n" if $i==11;
	    print printErrorFromOut();
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
# 1) Maude-ifies $file in case it is a .k|.kmaude file, generating a .maude file
# 2) It does the same recursively on each included file
# 3) Updates the global variables @all_sorts and @all_tokens
# - one to the list of sorts that are declared in the $file or in its included files
# - another to the list of tokens that appear in operations declared in the $file or its included files
sub maudify_file {
# Bind $file and $indent (the latter used for pretty printing when$verbose
    my ($file,$indent) = @_;
# If $file has extension .k, .kmaude or .maude then tests if $file exists and errors if not
    $file = getFullName($file);
    
    print $indent."Processing file $file\n" if $verbose;
    $indent .= "|   ";

    # hardcoded for avoiding maudification for shared.maude
    if ($file =~ /shared\.maude/)
    {
	return;
    }
    
# Slurp all $file into $_;
    local $/=undef; open FILE,"<",$file or die "Cannot open $file\n"; local $_ = <FILE>; close FILE;

# dots issue: change <cell>.</cell> into <cell> . </cell>    
    s!<(.*?)>\.</\1>!<$1> \. </$1>!g;
    
# Replacing dots    
    $_ = replace_dots($_);

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
	    push(@kmodules,$1);
	    $_ = maudify_module($file, $_);
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
	    s!\.k(maude)?\s*$!\.maude!s;
	}
	elsif (m!^(?:require)\s+(\S+)!) {
	    # print "File $file require: $1\n";
	    if (required($file, $1))
	    {
		maudify_file(File::Spec->catfile((fileparse($file))[1],$1),$indent);
		s!\.k(maude)?\s*$!\.maude!s;
		s!require!in!;
	    }
	    else
	    {
		s!require\s+\S+!!;
	    }
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
    
    my $maude_file = ($file =~ /^(.*)\.k(?:maude)?$/)[0].".maude";
    open FILE,">",$maude_file or die "Cannot write $maude_file\n";
    print FILE $maudified;
    close FILE;
}


sub maudify_module {
    (my $file, local $_) = @_;

    build_module_tree($file, $_);
#    print "Maudifying module with tokens @all_tokens\n";

# Step: Add whitespace between cell and Klabel
    s!(<\s*\/?\s*[^\s<]+\s*>)(')!$1 $2!g;

    # get KLabels
    my $decl = getKLabelDeclarations($_);

# Step: Add to @all_sorts all sorts defined a la Maude, with "sort(s)"
    add_sorts($_);
    
# Step: Freeze on-the-fly anonymous variable declarations
    s!_(:$ksort)!?$1!sg;
    s!(\?:$ksort)!freeze($1,"ANONYMOUS")!ge;
    # print  "Stage:\n$_\n\n";
    
# Step: Desugar syntax N ::= Prod1 | Prod2 | ... | Prodn
# At the same time, also declare N as a sort if it is not declared already
	s!(syntax\s+.*?)(?=$kmaude_keywords_pattern)!make_ops($1)!gse;
    # print  "Stage:\n$_\n\n";
    
# Step: Declare the on-the-fly variables
    $_ = on_the_fly_kvars($_);
    # print  "Stage:\n$_\n\n";
    
# Step: Reduce cell notation with _ to cell notation with ...
    s!<(\s*[^\s<]+\s*)_\s*>!<$1>... !gs;
    s!<\s*_(\s*/\s*[^\s>]+\s*)>! ...<$1>!gs;
    # print  "Stage:\n$_\n\n";
    
# Step: Declare cell labels as operations
    $_ = add_cell_label_ops($_);
    # print  "Stage:\n$_\n\n";
    
# Step: Add the module's newly defined tokens to @tokens
    add_tokens($_);
#     print  "Stage:\n$_\n\n";
    
# Step: Add missing spaces around tokens
    $_ = spacify($_);
#    print  "Stage:\n$_\n\n";
    
# Step: Change .List into (.).List , etc.
    s!\.(K|List|Set|Bag|Map)([^\w\{])!(.).$1$2!gs;
#    print  "Stage:\n$_\n\n";
    
# Step: Replace remaining _ by ? (spaces were put around _ by spacify)
    s! _ ! ? !gs;
    # print  "Stage:\n$_\n\n";
    
# Step: Change K attributes to Maude metadata
    s!(\[(?:\\.|[^\]])*\])!make_metadata($1)!gse;
    # print  "Stage:\n$_\n\n";
    
# Step: Change K statements into Maude statements
    s!((?:$kmaude_keywords_pattern).*?)(?=(?:$kmaude_keywords_pattern|$))!k2maude($1)!gse;
    # print  "Stage:\n$_\n\n";
    
# Step: Unfreeze everything still frozen
    $_ = unfreeze($_,"ANONYMOUS");
#    $_ = unfreeze($_);
    # print  "Stage:\n$_\n\n";

# Step: Add KLabel generated definitions - do that in shared.k for now
    if ($decl ne "")
    {
	$klabels .= $decl;
	s!mod(\s+)([\S]+)(\s+)is(\s+)!"mod$1$2$3is including K-SHARED .$4"!se;
	$mset = 1;
    }
#    print  "Stage:\n$_\n\n";
 
# Step: Add KLabel generated definitions
# s!(?=endk?m)!$decl!se;

# Step: register all subsort relations
    register_subsorts($_);

    return $_;
}


# Takes a syntax statement and extracts sorts, subsorts and operations
sub make_ops {
	local ($_) = @_;
#	print "make_ops:\n$_\n";

# Grab the result sort and the productions, as well as all spacing
 	my ($spaces1,$result_sort,$spaces2,$bnf,$productions,$spaces3) =  /^syntax(\s+)(\S*)(\s*)(::=)(.*?\S)(\s*)$/s;
#	print "$result_sort\n";
#	print "\$productions\n$productions\n";

# Report error and stop if the BNF form is not respected
	if (!defined($bnf)){
		print "ERROR: Syntactic categories must contain \"::=\" at line:\n$_\n";
		exit(1);
	}

# Report error and stop if the sort name does not match $ksort
	if ($result_sort !~ /^$ksort$/) {
	    print "ERROR: Sort \"$result_sort\" does not match the pattern \"$ksort\" in\n$_\n";
	    print "ERROR: Syntactic categories must currently match this pattern\n";
	    exit(1);
	}

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

#	    print "==============================\n";
#	    print "Production1:\n$production\n";
	    
# Replacing spaces in the production by "`"
#	        $production =~ s/\s+/`/gs;
	        
	    # Ugly hack: replace all strings with !&!&! 
	    # to avoid replacing spaces inside strings
	    my $strings = "";
	    $production =~ s/(\".*?\")/ { 
		$strings .= "!&!&!$1"; 
	    }
	    "!&!&!"
	    /gse;
	    
	    # replace spaces
	    $production =~ s/\s+/`/gs;

#	    print "Production2:\n$production\n";
	    # put the strings back
	    while ($strings =~ m/!&!&!(\".*?\")/g)
	    {
		my $str = $1;
		$production =~ s/!&!&!/$str/;
	    }
	    
	    
#	    print "Production3:\n$production\n";
#	    print "String:\n$strings\n";
#	    print "==============================\n";

# Removing unnecessary `
		$production =~ s/(^|$maude_special)`/$1/gs;
		$production =~ s/`($|$maude_special)/$1/gs;

# Add a latex attribute in case $latex and there is not already a user-defined one
		if (($latex || $pdf || $png || $ps || $eps || $crop) && ($attributes !~ /latex/)) {
		    my $latex_text = $production;
		    my $counter = 0;
		    $latex_text =~ s/([^_]+)/"\\terminal\{".make_latex($1)."\}"/gse;
		    $latex_text =~ s/_/$counter++;"{#$counter}"/ges;
		    $latex_text =~ s/"/&!&!&!/g;
		    if ($attributes eq "") {
			$attributes = "[]";
		    }
		    $attributes =~ s/^\[/[latex "$latex_text" /;
		}

# Generate the Maude replacement of the K syntactic construct
		$result .= ($production eq "_")
					? "$space4 subsort @sorts < $result_sort$space5 "
					: "$space4 op $production : @sorts -> $result_sort$space5$attributes ";
        }

# print "Done\n";
	return "$result$spaces3";
}


sub op_attribute {
	local ($_) = @_;
	/strict|prec|gather|metadata|latex|ditto|format|assoc|comm|id:/;
}


sub make_latex {
    local ($_) = @_;
    s/(\W)`/$1/gsm;
    s/`(\W)/$1/gsm;
    s/`/ /gsm;
    s/($latex_special)/\\$1/gsm;
    return $_;
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
    my $have_k_attributes = 0;

# Match the K specific attributes below and make them into metadata
# Right now it assumes that no \" can appear inside the metadata string
# Therefore, the latex attribute is expected to be outside
    s!(ditto|large|structural|hybrid|arity\s+\d+|(?:seq)?strict(?:\s*\((?:\s*\d+)*\s*\))?|latex\s+"[^"]*?")|metadata\s+"([^"]*?)"!
    my $out = "";
	if (defined $1) {
	    local $_ = $1;
            $have_k_attributes = 1;
	    if (/^latex\s+"([^"]*?)"$/gs) 
	    {
#		print "Latex attribute $1\n";
		push(@k_attributes, "latex(renameTo \\\\".get_newcommand($1).")") if ($latex || $pdf || $crop || $ps || $eps || $png);
	    }
	    else {
		push(@k_attributes, $_);
	    }
	    $out = "ditto" if $1 =~ m/ditto/;
	}
    else {
	push(@k_attributes, $2);
      }
    $out
      !gse;
    
#    print "K attributes: @k_attributes\n==============\n\n";

    if (@k_attributes) {
#	print "->@k_attributes<-\n";
	
# ugly hack for multiple occurences of ditto => eliminate duplicates from @k_attributes
#        my %hash = map { $_, 1 } @k_attributes;
#	my @unique_attr = keys %hash;
#	s!(.)\]$!"$1".(($1=~/[\s\[]/s) ? "":" ")."metadata \"@unique_attr\"\]"!se;
#	print "Keep: @unique_attr\nOut: $_\n";

#       original version
	s!(.)\]$!"$1".(($1=~/[\s\[]/s) ? "":" ")."metadata \"@k_attributes\"\]"!se;
#	print "$_\n";
    }
    elsif ($have_k_attributes) {
        s/^\s*\[\s*\]\s*$//gs;
    }
   return $_;
}


sub get_newcommand 
{
    local ($_) = @_;
    s/&!&!&!/"/g;
#    print "Apelat.\n";
    my $n = $newcommand_counter++;
    my $newcommand = $newcommand_prefix.chr(65 + $n % $newcommand_base);
    while ($n >= $newcommand_base) {
	$n /= $newcommand_base;
	$newcommand .= chr(65 + $n % $newcommand_base);
    }
    my @args = sort /{#(\d+)}/gms;
    my $max = $args[$#args];
    my $args = @args ? "\[$max\]" : "";
    s/\\\[/[/g;
    s/\\\]/]/g;
    s!(\{\#\d+\})(\{\#\d+\})!$1\\mathrel{}$2!g;
    push(@newcommands, "\\newcommand\{\\$newcommand\}$args\{$_\}");
    s/terminal/terminalNoSpace/gs;
    my $newcommandNoSpace = $newcommand."NoSpace";
    push(@newcommands, "\\newcommand\{\\$newcommandNoSpace\}$args\{$_\}");
#    print "Comanda: $newcommand\n";
    return $newcommand;
}


# Extract and declare on-the-fly kvariables
sub on_the_fly_kvars {
    local ($_) = @_;
    my %kvar_decls = ();
    s/\b($kvar):($ksort)/
    {
	if ($kvar_decls{$1}) {
	    if ($kvar_decls{$1} ne $2) {
		print "WARNING: Variable $1 declared with two distinct sorts ($kvar_decls{$1} and $2)\n" if $verbose; 
#		exit(1);
	    }
	} 
#    else {
	    $kvar_decls{$1} = $2;
#	}
	"$1:$2";
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
	       ? "ops ".join(" ",set($1 =~ /<\s*\/?\s*(.*?)\s*[\*\+\?]?\s*>/gs))." : -> CellLabel " : "");
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

    # Exclude strings because they can contain whitespaces
    my $strings = "";
    s/(\".*?\")/{$strings .= "$1!&!&!"; } "!&!&!"/gse;
    my @strs = split(/!&!&!/, $strings);
    
# Keep those operation names which have no _ or ` as tokens
    my @tokens = grep(!/[_`]/,split(/\s+/s));

#    print "TOKENS: @tokens\n";
# Extract all tokens that appear in operations
    @tokens = (@tokens, /$maude_special?($maude_unspecial+)/g) ;

    # Put the strings back
    my $index = 0;
    foreach my $token (@tokens)
    {
	while ($token =~ /!&!&!/g)
	{
	    $token =~ s/!&!&!/$strs[$index]/;
	    $index ++;
	}
    }
    
    
# Add allmeaningful tokens in @tokens to @all_tokens
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


# Report error and exit
sub throw_error
{
    my $err = shift;
    print "$err\n";
    exit(1);
}


sub add_subsorts
{
    my $supersorts = find_super_sorts();
    my @modules = split(/\s+/, getModuleList());
    my $k_sorts = "#Bag#BagItem#Bool#Builtins#CellLabel#Char#Int#K#KAssignments#KHybridLabel#KLabel#KResult#KResultLabel#KSentence#List#ListItem#List{KResult}#List{K}#Map#MapItem#Nat#NeBag#NeK#NeList#NeList{KResult}#NeList{K}#NeMap#NeSet#NzInt#NzNat#Set#SetItem#String#Zero#";
    my $dir = cwd;
    
    return if (scalar(@modules) == 0);
    return if ($supersorts eq "");
    
    my @sorts = split(/\s+/, $supersorts);
    $supersorts = "";
    foreach(@sorts)
    {
	$supersorts .= "$_ " if ($k_sorts !~ /#$_#/);
    }
    
    return if ($supersorts eq "");
    
    # get all supersorts in an array
    my @ssorts = split(/\s+/, $supersorts);

    # search through all modules
    foreach(@modules)
    {
	my $cmod = $_;
	# get sorts for current module
	my $sortlist = "#" . getModuleSorts($cmod) . "#" if defined(getModuleSorts($cmod));
	$sortlist =~ s/ /#/g if defined($sortlist);
	
	# if this module contains sorts
	# and it is a module which includes K
	# then add apropriate subsortations
	if (defined($sortlist) && includesK($cmod))
	{
	    # will collect declared sorts
	    my @decllist = ();
	    # search through supersorts all sorts contained by this module
	    foreach my $ss (@ssorts)
	    {
		push(@decllist, $ss) if ($sortlist =~ /#$ss#/);
	    }
	    
	    if (scalar(@decllist) > 0)
	    {
		# remove all declared sorts from ssorts.
#		for(my $i = 1; $i < scalar(@ssorts); $i++) 
#		{
#		    if ("@decllist" =~ /$ssorts[$i]/)
#		    {
#			delete $ssorts[$i];
#		    }		    
#		}
		
                # get module file
		my $file = getModuleFile($_);
	    
		# access its maude corresponding file
		$file =~ s/\.k$/\.maude/;

		# get content
		my $content = get_file_content("$dir/$file");
		
		my $o = "@decllist";
		$content =~ s/mod(\s+)$_(.*?)endm/mod$1$_$2 subsorts $o < K \. endm/sg;
		
		open FILE,">",$file or die "Cannot create $file\n";
		print FILE $content;
		close FILE;
	    }
	}
    }
    
#    print "SUPERSORTS: $supersorts\n";
#    print "MODULES: @modules\n";
}
