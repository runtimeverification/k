#!/usr/bin/env perl


#####################################
# Input:                            #
# ARGV[0] - program file            #
# ARGV[1] - language name           #
# ARGV[2] - syntax module           #
# ARGV[3] - sort of program         #
# ARGV[4] - program module          #
# ARGV[5] - tokenized program file  #
# ARGV[6] - identifiers file        #
# ARGV[7] - output file             #
#                                   #
# Output:                           #
#         - the program tokenized   #
#           in output file          #
#####################################


use strict;
use warnings;
use File::Basename;
use File::Spec;

if (@ARGV < 8)
{
    print "You must provide at least 8 arguments.\n";
    exit(1);
}

my $namespace = File::Spec->catfile((File::Basename::fileparse($0))[1], 'kast_utils.pl');
require $namespace;

our $comment;

# get arguments
my $pgm           = $ARGV[0];
my $lang          = $ARGV[1];
my $syntax_module = $ARGV[2];
my $sort_         = $ARGV[3];
my $pmod          = $ARGV[4];
my $tokenized     = $ARGV[5];
my $id            = $ARGV[6];
my $outfile       = $ARGV[7];


local $_ = get_file_content($tokenized);
my $ids  = get_file_content($id);


# transform program in equation
$_ = "eq $pgm = ( $_ ) .";

# add sort declaration
s/^/ops $pgm : -> $sort_ .\n/;

# add identifier declarations
s/^/ops $ids : -> #Id .\n/ if $ids ne "";

# add mod
s/^/mod $pmod is including $syntax_module .\n/;

# add endm
s/$/\nendm/;

# add imports
s/^/load .k\/$lang.maude\n/;



# put everything in a file
open FILE, ">", $outfile or die "Cannot open $outfile!\n";
print FILE;
close FILE;

