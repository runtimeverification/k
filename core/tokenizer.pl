#!/usr/bin/env perl


#####################################
# Input:                            #
# ARGV[0] - program file            #
# ARGV[1] - identifiers file        #
# ARGV[2] - tokens file             #
# ARGV[3] - output file             #
#                                   #
# Output:                           #
#         - the program tokenized   #
#           in output file          #
#####################################


use strict;
use warnings;
use File::Basename;
use File::Spec;

if (@ARGV < 4)
{
    print "You must provide at least 3 arguments.\n";
    exit(1);
}


my $namespace = File::Spec->catfile((File::Basename::fileparse($0))[1], 'common_functions.pl');
require $namespace;

$namespace = File::Spec->catfile((File::Basename::fileparse($0))[1], 'kast_utils.pl');
require $namespace;


our $comment;

# get arguments
my $pgm         = $ARGV[0];
my $id          = $ARGV[1];
my $tokens_file = $ARGV[2];
my $outfile     = $ARGV[3];

# collect tokens
my $tokens = get_file_content($tokens_file);
my @all = split("\n", $tokens);
my @all_tokens = split('\s', shift(@all));
my @all_syntax = split('\s', shift(@all));

# get program
local $_ = get_file_content($pgm);

# get identifiers
my @identifiers = split('\s', get_file_content($id));


my $ids = join(" ", @identifiers);


# remove comments
s!($comment)!
{
    local $_ = $1;
    s/\S//gs;
    $_;
}!gse;


# replace found ids with id("...");
# also use freeze/unfreeze for strings
my @ordered_ids = reverse length_sort(@identifiers);
s/(?<!\\)".*?(?<!\\)"/Freeze($&, "STRINGS")/sge;
for my $id (@ordered_ids)
{
    s/(?<![a-zA-Z_0-9])($id)(?![a-zA-Z_0-9])/id("$1")/sg;
}

# freeze also the construct id("identifier")
s/id\((?<!\\)".*?(?<!\\)"\)/Freeze($&, "STRINGS")/sge;

# spacify
my @tks = (@all_tokens, @all_syntax);
$_ = spacify($_, @tks);

# unfreeze everything
$_ = Unfreeze("STRINGS", $_);

# put everything in a file
open FILE, ">", $outfile or die "Cannot open $outfile!\n";
print FILE;
close FILE;


# an attempt to tokenize a program
sub spacify
{
    local $_ = shift;
    my @tokens = @_;
    
    my @temp = @tokens;
    @tokens = ();
    for my $tok (@temp)
    {
	my @keywords = split("_", $tok);
	for my $kwd (@keywords)
	{
	    push(@tokens, $kwd) if $kwd ne "";
	}
    }
    
    @tokens = reverse length_sort(set(@tokens));
    
    my @tkz = ();
    for my $tok (@tokens)
    {
	if ($tok ne ";")
	{
	    push(@tkz, quotemeta($tok));
	}
	else
	{
	    push(@tkz, $tok);
	}
    }
    
    my $tokens_pattern = join("|", @tkz);
    
    s/($tokens_pattern)/ $1 /sg;
    
    $_;
}
