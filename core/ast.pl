#!/usr/bin/env perl

use strict;
use warnings;
use XML::DOM;

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
    
    # simple strings
    if ($sort eq '#String')
    {
	return "# $op(.List{K})";
    }
    
    # numbers
    # naturals
    if ($op eq "sNat_")
    {
	my $number = $attrs->getNamedItem("number")->getNodeValue;
	return "# $number(.List{K})";
    }

    # integers
    if ($op eq "-Int_")
    {
	my $int = get_ast_from_node($children->item(1));
	$int =~ s/^#\s/# -/;
	return $int;
    }
    
    # builtin sorts default
    return "# $op(.List{K})" if ($sort =~ /^#/);
    
    # empty appliances default
    return "'$op(.List{K})" if ($content =~ /^\s*$/);
    
    "'$op($content)";
}

1;
