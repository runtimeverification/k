#!/usr/bin/env perl

use strict;
use warnings;
use File::Basename;
use File::Spec;

##################################################
# Input:                                         #
# 1. ARGV[0] - the program file                  #
# 2. ARGV[1] - tokens file exported by kompile!  #
# 3. ARGV[2] - filename of the file which will   #
#              store the identifiers             #
#                                                #
# If these arguments are not provided then the   #
# program will finish with an error              #
#                                                #
# Output: filename will contain all identifiers  #
# from program file computed using tokens        #
##################################################


if (@ARGV < 3)
{
    print "You must provide at least 3 arguments.\n";
    exit(1);
}

# include kast_utils
my $namespace = File::Spec->catfile((File::Basename::fileparse($0))[1], 'kast_utils.pl');
require $namespace;

our $comment;

# get arguments
my $pgm         = $ARGV[0];
my $tokens_file = $ARGV[1];
my $outfile     = $ARGV[2];

# collect tokens
my $tokens = get_file_content($tokens_file);
my @all = split("\n", $tokens);
my @all_tokens = split('\s', shift(@all));
my @all_syntax = split('\s', shift(@all));

# will keep all identifiers
my @identifiers = ();

# get the program
local $_ = get_file_content($pgm);

# remove comments
s!($comment)!
{
    local $_ = $1;
    s/\S//gs;
    $_;
}!gse;


# remove strings
s/(?<!\\)".*?(?<!\\)"//sg;

# syntax contains undescores:
# remove them and keep only keywords
my @temp = ();
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

# remove syntax
for my $syntax_item (@all_syntax)
{
    # remove bounded alpha-characters
    if ($syntax_item =~ /\b[a-zA-Z_]+\b/s)
    {
	s/\b($syntax_item)\b/ /sg;
    }
}

# remove the rest of tokens (in reversed topological order)
# make sure this is still needed ...
for my $token (@all_tokens)
{
    s/\Q$token\E/ /sg;
}


# collect identifiers
s/\b([a-zA-Z_\$][a-zA-Z_0-9]*)(?=(\s|$))/
{
    push (@identifiers, $1);
    "";
}/sge;

# make identifiers unique
@identifiers = set(@identifiers);

# put everything in a file
open FILE, ">", $outfile or die "Cannot open $outfile!\n";
print FILE "@identifiers";
close FILE;
