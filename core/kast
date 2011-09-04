#!/usr/bin/env perl

# imports
use strict;
use warnings;
use Getopt::Long;
use File::Spec;
use File::Basename;

################
# Variables    #
################

# options
my $help;

my $pgm           = "?";
my $pmod          = "?";
my $cfile         = "?";
my $sort_         = "?";
my $syntax_module = "?";
my $verbose       = 0;


# utils
my @all_tokens  = ();
my @all_syntax  = ();
my @identifiers = ();

# comments
my $comment = join("|", (                                                                                                      
    "\\/\\/.*?\n",                                                                                                       
    "\\/\\*.*?\\*\\/",                                                                                                   
    "---\\(.*?---\\)",                                                                                          
    "---.*?\n",                                                                                                  
    "\\*\\*\\*\\(.*?\\*\\*\\*\\)",                                                                              
    "\\*\\*\\*.*?\n" )); 



################
# main         #
################

# read command line arguments
usage() if (@ARGV < 1 or
    ! GetOptions('help|?' => \$help,
	'pgm=s'     => \$pgm,
	'pmod=s'    => \$pmod,
	'cfile=s'   => \$cfile,
	'sort=s'    => \$sort_,
	'smod=s'    => \$syntax_module,
	'v|verbose' => \$verbose,
    ) or defined $help );


# check if command line options are set.
arg_error("Please set all command options; -pgm is not given!") if $pgm eq "?";
arg_error("Please set all command options; -pmod is not given!") if $pmod eq "?";
arg_error("Please set all command options; -cfile is not given!") if $cfile eq "?";
arg_error("Please set all command options; -sort is not given!") if $sort_ eq "?";
arg_error("Please set all command options; -smod is not given!") if $syntax_module eq "?";


# get the program
local $_ = get_file_content($pgm);
my $temp = $_;

# get tokens
my $dir = dirname($cfile);
my $tokens_file = File::Spec->catfile($dir, ".k/all_tokens.tok");
my $tokens = get_file_content($tokens_file);
my @all = split("\n", $tokens);
@all_tokens = split('\s', shift(@all));
@all_syntax = split('\s', shift(@all));

print "Tokens file found ...\n" if $verbose;
print "TOKENS: @all_tokens\n@all_syntax\n\n" if $verbose;
print "Prepare for identifying identifiers ...\n" if $verbose;

# remove comments
s!($comment)!
{
    local $_ = $1;
    s/\S//gs;
    $_;
}!gse;
print "Removed tokens ...\n" if $verbose;


# remove strings
s/(?<!\\)".*?(?<!\\)"//sg;
print "Removed strings ...\n" if $verbose;

my @temp = ();
# take care of syntax items
for my $syntax_item (@all_syntax)
{
    my @keywords = split("[^a-zA-Z]+", $syntax_item);
    for my $kwd (@keywords)
    {
	push(@temp, $kwd);
    }
    
    push(@temp, $syntax_item) if !(scalar @keywords > 0);
}

@all_tokens = reverse length_sort(@all_tokens);
@all_syntax = reverse length_sort(@temp);

# print "TOKENS: @all_tokens\n\n@all_syntax\n\nPROGRAM:$_\n\n";

# remove all syntax constructs
for my $syntax_item (@all_syntax)
{
    # remove bounded alpha-characters
    if ($syntax_item =~ /\b[a-zA-Z_]+\b/s)
    {
	s/\b($syntax_item)\b/ /sg;
    }
    
#    print "STEP |$syntax_item| : $_\n\n";
}

# remove tokens (in reversed topological order)
# make sure this is still needed ...
for my $token (@all_tokens)
{
    s/\Q$token\E/ /sg;
}


# collect identifiers
s/\s([a-zA-Z_]+)\s/
{
    push (@identifiers, $1);
    " ";
}/sge;

# unique Ids
@identifiers = set(@identifiers);

print "Found identifiers: @identifiers\n\n" if $verbose;



# Creating the K module
$_ = $temp;

$pgm =~ s/\..*$//s;
my $ids = join(" | ", @identifiers);


my $header = "kmod $pmod is including $syntax_module\n\n  syntax $sort_ ::= $pgm\n";
$header .= "  syntax #Id ::= $ids\n\n  " if $ids ne "";



# append module "header"
s/^/$header
  macro $pgm = ( /s;
 
# append end
s/$/)\n\nendkm/s;



# save in $pgm_cast.k
open FILE, ">", "$pgm\_cast.k" or die "Cannot save in file $pgm\_cast.k";
print FILE;
close FILE;

print "Save everything in $pgm\_cast.k\n\nDone.\n" if $verbose;

################
# end main     #
################





###########
# utils   #
###########

# print a help message and exit
sub usage
{
    print "Unknown option: @_\n" if @_;
    print "usage: cast -pgm program_name -pmod program_module -cfile compiled_file -sort pgm_sort -smod syntax_module\n\t[-verbose]\n\n
  Options:
  \t-verbose: verbose mode
  \t-pgm    : specify the file where the program is.
  \t-pmod   : specify the name of the module which will wrap the program
  \t-cfile  : specify a k compiled file
  \t-sort   : specify program sort
  \t-syntax : specify the syntax module name\n\n";

    exit;
}

# print an error message if arguments not set
sub arg_error
{
    print shift . "\n";
    usage();
}

# returns file content as string
sub get_file_content                                                                                                              
{                                                                                                                                 
    my $filename = shift;                                                                                                         
    
    open FILEHANDLE, "<", $filename or die "Could not open $filename:\n$!";                                                       
    my @input = <FILEHANDLE>;                                                                                                     
    close FILEHANDLE;                                                                                                             
    
    return join("", @input);                                                                                                      
}

# sorts an array by length of its elements
sub length_sort
{
    sort {length $a <=> length $b} @_;
}

# get set-like array from another array
# get rid of duplicates
sub set
{
    if (@_)
    {
	my %map = map { $_ => 1 } @_;
	return keys %map;
    }
    
    ();
}
