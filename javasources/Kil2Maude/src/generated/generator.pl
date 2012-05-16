#!/usr/bin/env perl

use strict;
use warnings;
use XML::DOM;

print "Usage: ./generator.pl <xml-def> <constants-draft> <factory-draft> <placeholder-draft>\n" if (@ARGV < 4);

my $xml_def = $ARGV[0];
my $constants = $ARGV[1];
my $constants_file = "Constants.java";
my $factory = $ARGV[2];
my $factory_file = "TagFactory.java";
my $placeholder = $ARGV[3];

my @tags  = ();
my @attrs = ();

# process XML
my $module_tag = "module";
my $parser = new XML::DOM::Parser;
my $doc = $parser->parsefile($xml_def);
my $nodes = $doc->getElementsByTagName($module_tag);

my $n = $nodes->getLength;
for (my $i = 0; $i < $n; $i ++)
{
    visit($nodes->item($i));
}
      
sub visit
{
    my $node = shift;

#    print "NT: " . $node->getNodeName . " : " . $node->getNodeType . "\n";
    if ($node->getNodeType == ELEMENT_NODE)
    {
	push(@tags, $node->getNodeName);
	
	my $children = $node->getChildNodes;
	my $length = $children->getLength;
	for (my $j = 0; $j < $length; $j ++)
	{
	    visit($children->item($j));
	}

    }

    my $attributes = $node->getAttributes;
    if (defined $attributes)
    {
	my $nmlength = $attributes->getLength;
	for(my $j = 0; $j < $nmlength; $j ++)
	{
	    push(@attrs, $attributes->item($j)->getNodeName);
	}
    }
}

@tags  = unique(@tags);
@attrs = unique(@attrs);

# print "ELEMENT: " . ELEMENT_NODE . "\nATTR: " . ATTRIBUTE_NODE . "\n";
# print "TAGS:\n" . join("\n", @tags) . "\n\nATTR:\n" . join("\n", @attrs);



###############
## Constants ##
###############

my $cts = "";
foreach (@tags)
{
    $cts .= "\n\tpublic static final String " . getTag($_) . " = \"$_\";";
}

my $att = "";
foreach (@attrs)
{
    $att .= "\n\tpublic static final String " . getAttr($_) . " = \"$_\";";
}

# print $cts;
# print $att;

my $consts = get_file_content($constants);
$consts =~ s/ConstantsPH/Constants/sg;
$consts =~ s/\/\/PLACEHOLDER/\/\/Tags constants$cts\n\n\t\/\/Attributes constants$att\n/sg;
save_content_in_file($consts, $constants_file);




#################
## Tag Factory ##
#################

my $ifs = "";
foreach (@tags)
{
    $ifs .= "\n\tif (Constants." . getTag($_) . ".equals(element.getNodeName()))\n\t\treturn new " . getTag($_) . "(element, consMap);";
}

# print $ifs;

my $fact = get_file_content($factory);
$fact =~ s/TagFactoryPH/TagFactory/sg;
$fact =~ s/\/\/PLACEHOLDER/$ifs/sg;
save_content_in_file($fact, $factory_file);







######################
## Class generation ##
######################

my $classtemplate = get_file_content($placeholder);
my $temp;
my $classname;
foreach (@tags)
{
    $temp = $classtemplate;
    $classname = getTag($_);
    
    $temp =~ s/PLACEHOLDER/$classname/sg;
    
    save_content_in_file($temp, "$classname.java") if !(-e "$classname.java");
}





###########
## utils ##
###########

sub save_content_in_file
{
    my ($content, $file) = (shift, shift);
    open FILE, '>', $file or die "Cannot create $file!\n";
    print FILE $content;
    close FILE;
}


sub getTag
{
    uc(shift) . "_$_" . "_TAG";
}
sub getAttr
{
    uc(shift) . "_$_" . "_ATTR";
}

sub unique
{
    my %seen = ();
    grep { ! $seen{$_} ++ } @_;
}

sub get_file_content
{
    my $filename = shift;
    
    open FILEHANDLE, "<", $filename or die "Could not open $filename:\n$!";
    my @input = <FILEHANDLE>;
    close FILEHANDLE;
    
    return join("", @input);
}
