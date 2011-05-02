#!/usr/bin/perl -w

use strict;

# this does
#1. read a <program.c> and some optional input (integer stream) form <program>
#2. transform <program.c> in <program.k>
#3. kompile <program.k> with kompile.pl -pgm (etc...)
#4. create a script <program.exe.pl> that runs the program with the initial parameters

############### specify the values below
# this 2 values are required for the program transformation
my $requirements = "
load cink-compiled
load sym-int
load cink-syntax
"; # these are the loads necesary for compilation

my $include_modules = "CINK-SYNTAX";	#the module required to compile (usualy the syntax)

# initial settings
my $cmod = "CINK";	# the module where the language is
my $kompile_path = "../../../../tools/kompile.pl";	# path to kompile.pl

my $maude_path = "maude";	# path to maude
my $format_yml = "./example.yml";	# path to example.yml
my $filter = "../filterOutput";		# path to filterOutput


########################## you need to specify all of the above

my $module_name = "";    # module name
my $macro_name = "";	#macro name

my $input_file = "maude_in.txt";
my $output_file = "maude_out.txt";
my $error_file = "maude_err.txt";

# the input imp source
my $input_source;

# the output k source
my $output_source;

# the input file name
my $file;
if (scalar(@ARGV) < 1)
{
    print "USAGE: <file to compile> [params]\n\n";
    exit(1);
}
$file = $ARGV[0];

shift(@ARGV);
my $args = ".List{K}";

if (scalar(@ARGV))
{
    foreach(@ARGV)
    {
		$_ = "Int $_(.List{K})";
    }
    $args = join ( ",,", @ARGV);
}


# main tasks
read_input($file);
translate();
save_output($file);

# compile the generated file with kompile.pl -pgm ...
run_kompile();









# translates C into K
sub translate
{
	local $_ = "$input_source";

	# "globals" which will contain data in order to generate k file.
	my $macro_content = $_;  # macro content
	#my $include_modules = ""; #include modules
	my $heap_name = "";      # heap name
	my $id_list = "";        # list of ids
	my $int = "";           # ?Int
	my $freeint = "";        # FreeInt
	my $seq1 = "";           # ?Seq
	my $seq2 = "";           # !Seq
	my $freeseq = "";        # FreeSeq

	# utility declarations
	my $id = "[a-zA-z][\-_\.a-zA-Z0-9]*";    # it looks like an id...
	my $specialC = "[\"<>']*"; # include's special and quoted
	my $specialId = "$specialC$id$specialC"; # combined ids
	my $declaration = "void|struct|int|#include";                # available types


	###############
	# Module name          #
	##############

	$module_name = $file;
	$module_name =~ s/\.[a-zA-Z]*//g;
	$macro_name = $module_name;
	$module_name = uc($module_name);

	#############
	# Include modules #
        #############

	$include_modules = $1 if /\/\/\s+uses\s+the\s+modules:(.+?)\s+\n/;
	s/\/\/\s+uses\s+the\s+modules:(.+?)\s+\n//g;
	$include_modules =~ s/^\s+//g;
	$include_modules =~ s/\s+$//g;
	$include_modules =~ s/\s+/ + /g;


        ##############
	# Freeze comments   #
	##############
	my $comments = "";
	s/(\/\*.*?\*\/)/ {
		$comments .= "!&!&!$1";
	}
	"!&!&!"
	/gse;


	#############
	# Get id list #
	#########
	while (/($declaration)[\s\*]+($specialId)/g)
	{
#		print "$1 ID: $2\n";
		$id_list .= "$2 ";
	}
	while (/($declaration)[\s\*]+($specialId)[\s\*]+($specialId)/g)
	{
#		print "$1 $2 ID: $3\n";
		$id_list .= "$3 ";
	}
	$id_list = reduce($id_list);
#	print "List: $id_list\n\n";


	################
	# Unfreeze  comments #
	###############

	while ($comments =~ m/!&!&!(\/\*.*?\*\/)/g)
	{
		my $str = $1;
		s/!&!&!/$str/;
	}
#	print "Comments:\n $comments\n\n";

        $_  = "$input_source";

	######
	# ?Int  #
	#####
	while(/(\?[a-z]+'?)[:\s]+/g)
	{
#		print "Match: $1\n";
		$int .= "$1 ";
	}
	$int = reduce($int);
	$int =~ s/\?/`\?/g;

	######
	# ?Seq  #
	#####
	while(/(\?[A-Z]+'?)[^a-z]/g)
	{
#		print "Match: $1\n";
		$seq1 .= "$1 ";
	}
	$seq1 = reduce($seq1);
	$seq1 =~ s/\?/`\?/g;


	######
	# !Seq  #
	#####
	while(/(![A-Z]+'?)[^a-z]/g)
	{
#		print "Match: $1\n";
		$seq2 .= "$1 ";
	}
	$seq2 = reduce($seq2);
	$seq2 =~ s/!/`!/g;


	#########
	# FreeSeq  #
	########
	while(/\(\s*([A-Z]+'?)\s*\)/g)
	{
#		print "Match: $1\n";
		$freeseq .= "&$1 ";
	}
	$freeseq = reduce($freeseq);
	$freeseq =~ s/&/`/g;


# append kmod header
	$output_source  = "$requirements\n";
	$output_source .= "kmod $module_name is including $include_modules\n";

	# append syntax statements, decl and macro content.
	$output_source .= "\tsyntax Id ::= $id_list \n";
	$output_source .= "\tsyntax ?Int ::= $int \n" if ($int ne "");
	$output_source .= "\tsyntax FreeInt ::= $freeint \n" if ($freeint ne "");
	$output_source .= "\tsyntax ?Seq ::= $seq1 \n" if ($seq1 ne "");
	$output_source .= "\tsyntax !Seq ::= $seq2 \n" if ($seq2 ne "");
	$output_source .= "\tsyntax FreeSeq ::= $freeseq \n" if ($freeseq ne "");
	$output_source .= "\n\tsyntax Pgm ::= $macro_name\n\n";
	$output_source .= "\tmacro $macro_name = \n$macro_content\n\nendkm\n";

#	print $output_source;
	#~ print ("Finished\n");
}

# sub read a imp file content and stores it into $input_source
sub read_input
{
    open FILE, "<", $file or die "Could not open $file:\n$!";
    my @input = <FILE>;
    $input_source = "@input";
    close FILE;
}


# sub saves a k source into a file
sub save_output
{
    # replace filename`s extension
    $file =~ s/\.c$/\.k/;

    open FILE, ">", $file or die "Could not open $file:\n$!";
    print FILE $output_source;
    close FILE;
}

# sub eliminate duplicates from a string
# and return a string with words separated by '|'
sub reduce 
{
    my @array = split(/\s+/, (shift));

    # eliminate duplicates
    my %comb;
    @comb{@array} = ();
    my @uniq = sort keys %comb;
    
    join(" | ", @uniq);
}
    
sub get_file_content
{
    my $filename = shift;
    
    open FILE, "<", $filename or die "Could not open $filename:\n$!";
    my @input = <FILE>;
    close FILE;
    
    return "@input";
}

# Running Maude (cross platform)
sub run_kompile {
#    my ($message,@commands) = @_;
#    print $message;
#    open FILE,">",$input_file or die "Cannot create $input_file\n";
#    print FILE "\n@commands\n";
#    close FILE;
    
    # call maude
    print "$kompile_path -pgm $macro_name.k -cmod $cmod -pmod $module_name -pname $macro_name\n";
    my $status = system("$kompile_path -pgm $macro_name.k -cmod $cmod -pmod $module_name -pname $macro_name  >$output_file 2>$error_file");
    if (($status >>= 8) != 0)
    {
	my $err = get_file_content($error_file);
	$err =~ s/\n.*?$//sg;
	print "$err\nFailed to run kompile.pl.\nExit status $status.\n" ;
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
	local $/=undef;
	open FILE,"<",$output_file or die "Cannot open $output_file\n";
	local $_ = <FILE>;
	close FILE;
	return $_;
    }
    else {
	print "\nMaude cannot be detected: the command $kompile_path does not execute\n";
	print "Aborting the compilation\n";
	clean();
	exit(1);
    }
}

my $run_file = '#!/usr/bin/perl -w

#this is a generated file
use strict; 
use warnings;


# initial settings
my $maude_path = "' . $maude_path . '";
my $test_file = "' . "$macro_name-compiled.maude" . '";
my $format_yml = "' . $format_yml . '";
my $filter = "' . $filter . '";

my $input_file = "maude_in.txt";
my $output_file = "maude_out.txt";
my $error_file = "maude_err.txt";

my $program = "'. $macro_name .'";

my $args = "'.$args.'";

# run maude
local $_ = run_maude("Running maude ...\n",
    "load $test_file\n",
    "rew run( \'$program , $args ) .\n",
    "quit\n"
);

# print "$_\n";
open FILE,">",$output_file or die "Cannot create $output_file\n";
print FILE;
close FILE;

system ("./$filter $output_file $format_yml");

# make clean
unlink($input_file);
unlink($error_file);
unlink($output_file);


# Running Maude (cross platform)
sub run_maude {
    my ($message,@commands) = @_;
    print $message;
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
	local $/=undef;
	open FILE,"<",$output_file or die "Cannot open $output_file\n";
	local $_ = <FILE>;
	close FILE;
	return $_;
    }
    else {
	print "\nMaude cannot be detected: the command $maude_path does not execute\n";
	print "Aborting the compilation\n";
	clean();
	exit(1);
    }
}


sub get_file_content
{
    my $filename = shift;
      
    open FILE, "<", $filename or die "Could not open $filename:\n$!";
    my @input = <FILE>;
    close FILE;
    
    return "@input";
}

';

open (MYFILE, ">$macro_name.exe.pl");
print MYFILE ($run_file);

chmod (0755, "$macro_name.exe.pl") or die "Couldn't chmod $macro_name.exe.pl: $!";

