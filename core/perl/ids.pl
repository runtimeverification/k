#!/usr/bin/env perl

use strict;
use warnings;
use POSIX;

my $ksort = "[A-Z#][A-Za-z0-9\\`\\+\\?\\!#]*(?:\\{[A-Z#][A-Za-z0-9\\`\\+\\?\\!]*\\})?";
my @kmaude_keywords = qw(context rule macro eq ceq configuration op ops syntax kvar sort sorts subsort subsorts including kmod endkm mb tags);
my $kmaude_keywords_pattern = join("|",map("\\b$_\\b",@kmaude_keywords));


sub solve_ids
{
    local $_ = shift;
    my $temp = $_;
    
    # iterate through syntax declarations
    while ($temp =~ /(syntax\s+#Id\s*::=(.*?(\s*\[\s*metadata.*?\])?))\s*(?=$kmaude_keywords_pattern)/sg)
    {
	# keep syntax declaration
	my $syntax_item = $1;
	my $productions = $2;
	my $gen_eqs = "";
        my $gen_prods = "";
        my $gen_prod = "";
        my $metadata = "";
        my $new_production = "";
	
	# productions
	my @productions = ($productions =~ /(.*?\S.*?(?:\s\|\s|$))/gs);

	# iterate through productions
	foreach my $production (@productions)
	{
	    # Removing the | separator
	    $production =~ s/(\s)\|(\s)/$1$2/gs;
            $new_production = " $production";
	    $new_production =~ s/\s*\[\s*metadata "(.*?)"\]//gs;
            $metadata = $1;
            if ($new_production !~ /(?<=\s)[A-Z#]/gs) {
	      $new_production =~ s/\s|`//gs;
              $gen_prod = "$new_production \[metadata \"$metadata parser=()\"\]";
              $gen_eqs .= " eq $new_production = #id(\"$new_production\") \[metadata \"parser=() generated=()\" \]\n";
            } else {
              $gen_prod = $production;
            }

            if ($gen_prods eq "") {
              $gen_prods = "syntax #Id ::= $gen_prod"
            } else {
              $gen_prods .= " | $gen_prod";
            }
       	}
	
	s/\Q$syntax_item\E/$gen_prods\n\n$gen_eqs\n/s;	
    }
	    
    $_;
}


