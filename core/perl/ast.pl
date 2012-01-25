#!/usr/bin/env perl

use strict;
use warnings;
use XML::DOM;

my $kind="";
my $k_prelude = File::Spec->catfile($ENV{K_BASE}, "core", "maude", "lib", "k-prelude");

sub get_ast
{
    # get file
    my $astfile = shift;
    
    # create parser
    my $parser = new XML::DOM::Parser();
    
    # parse file
    my $doc = $parser->parsefile($astfile);
    
    # get result node
    my $result = $doc->getElementsByTagName("result");
    
    # get the first result (which should be only one I think :-D )
    # get parse__ term
    $result = $result->item(0)->getChildNodes()->item(1);
 
    local $_ = get_ast_from_node($result);
    if ($kind ne "") 
    {
	print"Subterm $kind";
	exit(1);
    }
    
    # remove parse_
    s/^\'parse_\(//sg;
    s/\)$//sg;

    $_;
}

sub get_ast_from_node
{
    my $node = shift;
    
    my $attrs = $node->getAttributes;
    my $children = $node->getChildNodes();
    
    my $op = $attrs->getNamedItem("op")->getNodeValue;
    my $sort = $attrs->getNamedItem("sort")->getNodeValue;
#    print "\t SORT: $sort";
    
    my $content = "";
    for my $i (0 .. $children->getLength - 1)
    {
	
	my $child = $children->item($i);
#	print "\tINSPECT: " . $child->toString . "\n"; 
	if ($child->getNodeTypeName eq "ELEMENT_NODE")
	{
	    # print $child->toString . "\n";
	    $content .= get_ast_from_node($child) . ",,";
	}
    }
# print "Op: $op; Sort: $sort; Content: $content\n";
    $content =~ s/,,$//s;

    # #id("identifier")
    if ($sort eq '#Id')
    {
	if ($op =~ /^\s*#id/)
	{
	    my $ch = $children->item(1)->getAttributes->getNamedItem("op")->getNodeValue;
	    return "# $op($ch)(.List{K})";
	}
	     
	return "# $op(.List{K})";
    }
# print "RUN1: Op: $op; Sort: $sort; Content: $content\n";
    
    # simple strings
    if ($sort eq '#String')
    {
	return "# $op(.List{K})";
    }
# print "RUN2: Op: $op; Sort: $sort; Content: $content\n";
    
    # numbers
    # naturals
    if ($op eq "sNat_")
    {
	my $number = $attrs->getNamedItem("number")->getNodeValue;
	return "# $number(.List{K})";
    }
# print "RUN3: Op: $op; Sort: $sort; Content: $content\n";

    # integers
    if ($op eq "-Int_")
    {
	my $int = get_ast_from_node($children->item(1));
	$int =~ s/^#\s/# -/;
	return $int;
    }
# print "RUN4: Op: $op; Sort: $sort; Content: $content\n";
    
    # builtin sorts default
    my $allksorts = get_builtin_sorts();
    $allksorts = $1 if ($allksorts =~ m/NeSortSet:(.*?Bye)\./sg);
    if ($allksorts =~ /\Q\'$sort\E/sg)
    {
#	print "\n$sort matched in $allksorts\n\n";
#	print "RUN41: Op: $op; Sort: $sort; Content: $content\n";      
	return "# $op(.List{K})" 	
    }
    elsif ($sort =~ /^#/sg)
    {
#	print "RUN41: Op: $op; Sort: $sort; Content: $content\n";
	return "# $op(" . flat($content) . ")(.List{K})";
    }
# print "RUN5: Op: $op; Sort: $sort; Content: $content\n";
    
    # empty appliances default
    return "'$op(.List{K})" if ($content =~ /^\s*$/);

    if ($sort =~ /^\[/ && $kind eq "") 
    {
	$kind = "'$op($content) parses to kind $sort.\nIt seems that Maude is unable to parse this subterm.\nThis could be a problem in your semantics.\n";
    }
    
    "'$op($content)";
}

sub flat
{
    my $r = shift;
#    print "RECV: $r\n";
    $r =~ s/#\s//sg;
    $r =~ s/\(.List\{K\}\)//sg;
    $r =~ s/,,/,/sg;
    $r;
}

sub get_builtin_sorts
{
    my $tmp = "tempfile.maude";
    open FILE,">", $tmp or die "Cannot create $tmp\n"; 
    print FILE "in $k_prelude\nred in META-LEVEL : getSorts(upModule('K, true)) .\nq\n";
    close FILE;
    
    my $out = `maude $tmp`;

    unlink($tmp);
    return $out;
}

1;
