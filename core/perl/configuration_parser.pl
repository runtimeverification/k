###########################################################################
#    Copyright (C) 2011 Andrei Arusoaie                                   # #                                                                         #
#    This file is free software; you can redistribute it and/or modify    #
#    it under the terms of the GNU General Public License as published by #
#    the Free Software Foundation; either version 2 of the License, or    #
#    (at your option) any later version.                                  #
#                                                                         #
#    This program is distributed in the hope that it will be useful,      #
#    but WITHOUT ANY WARRANTY; without even the implied warranty of       #
#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the        #
#    GNU General Public License for more details.                         #
###########################################################################


#!/usr/bin/env perl -w
my $path = ".";

BEGIN {
    $path = (File::Basename::fileparse($0))[1];
}


use lib $path;
$path = (File::Basename::fileparse($0))[1];
$path = File::Spec->rel2abs($path);






# imports
use Switch;
use File::Spec;
use XML::DOM;

use Text::Wrap;
$Text::Wrap::columns = 75;


#########
# SETUP #
#########

our @checksum_files; # used in checksumming kompile program to detect version changes

# keep k valid attributes and values into this map
my %xml_attr = ();

# my container for storing exceptions
# it is used to simulate a try-catch like mechanism
my @container = ();

# open/closed try-catch "session"
my $session = 0;

# K configuration files
# my $k_attributes = "k_attributes.xml";
my $k_attributes = File::Spec->catfile((File::Basename::fileparse($0))[1], 'perl', 'k_attributes.xml');
push(@checksum_files, $k_attributes);

# This is specific to $k_attributes configuration file
# keep k attributes tag names
my $k_attr_tag = "k-attribute";
my $k_attr_name = "name";
my $k_attr_values = "values";

# temporary files
my $temporary = "cfg_temp.tmp";
my $xml_parser = "xml-parser.pl";

# temporary variables
my $temp_var = "";

# keep the DOM TREE of the configuration
my $dom;

# configuration (xml) string
my $configuration = "";

# configuration starting line
my $config_line = 0;

# generated TAG name
my $TAG = "K-TOOL-GENERATED-ROOT";

# current file
my $file = "unknown file";

###############################
# Specific ERRORS definitions #
###############################

my $ERROR                                 = 10;      # general error

my $INVALID_ATTRIBUTE_ERROR             = 20;    # thrown when finding attributes which 
                                                # are not allowed in a K configuration

my $INVALID_VALUE_FOR_ATTRIBUTE_ERROR     = 30;    # thrown when finding invalid values
                                                # for a given K attribute

my $INVALID_XML                         = 40;    # thrown when xml cannot be parsed



#############
# END SETUP #
#############





# Args: configuration xml-like string, configuration starting line number
# Return: void
# This should be the only public method
# Multiple jobs:
#         - loads the K specific attributes
#         - parses the configuration
sub parse_configuration
{
    # get configuration content and starting line number.
    ($configuration, $config_line, $file) = (shift, shift, shift);

    if (!(-e $file))
    {
	# silently ignore the rest
	return;
    }
    
    # start a "try-catch" session
    try();
    # {    
        # load k configuration file
        load_K_specific_attributes($k_attributes);

        # parse the configuration
        parse_XML_K_configuration($configuration);
    # }
    # catch the exceptions
    catch();

    # clean temp
    clean_();
}



# Args: xml file
# Return: void
# Receives an xml file which contains all attributes
# allowed in a K configuration and their valid values
# loads all these attributes as a pair in %xml_attr (map): 
#           attribute_name -> values
sub load_K_specific_attributes
{
    # get the xml file 
    my $xml = shift;

    # create a new parser
    my $parser = new XML::DOM::Parser();

    # create doc tree
    my $doc = $parser->parsefile($xml);

    # get all k attributes
    my $nodes = $doc->getElementsByTagName($k_attr_tag);

    # get number of k attributes
    my $n = $nodes->getLength;

    # add pairs (k-attribute-name, k-attribute-values) to map %xml_attr
    for (my $i = 0; $i < $n; $i++)
    {
        # get node object
        my $node = $nodes->item($i);

        # get $k_attr_name and $k_attr_values attributes for the current node
        my $k_attribute_name = $node->getAttributeNode($k_attr_name)->getValue;
        my $k_attribute_values =  $node->getAttributeNode($k_attr_values)->getValue;

        # add pair to map
        $xml_attr{$k_attribute_name} = $k_attribute_values;
    }    

    # Avoid memory leaks
    $doc->dispose();
}

# Args: an xml-like string
# Return: XML::DOM::Document
# Parse an XML and report errors if any
# If parse ok, then return DOM tree.
sub parse_xml
{
    my $xml = shift;
    
    # hack
    $xml =~ s/<\s*([a-zA-Z\-]+)\s*>/<$1>/sg;
    $xml =~ s/<\s*\/\s*([a-zA-Z\-]+)\s*>/<\/$1>/sg;


    # save content in file
    open FILE, '>', $temporary;
    print FILE $xml;
    close FILE;

    # create external parser
    create_xml_parser();
    
    # call external xml parser script
    # if this script dies then report an error
    my $sys_call = `perl $xml_parser $temporary 2>&1`;

    # verify the parsing result
    if ($sys_call)
    {
        # report specific xml parsing error
        error_report($INVALID_XML, $sys_call);
    }
    else
    {
        # create a new parser
        my $parser = new XML::DOM::Parser();

        # create doc tree
        my $doc = $parser->parse($xml);
    
        # return document tree
        return $doc
    }

    # return undef if error
    return undef;
}

# Args: a string which contains a K configuration
# Return: void
# Parse an XML configuration and report errors if any.
sub parse_XML_K_configuration
{
    # K configuration
    local $_ = "<$TAG>" . (shift) . "</$TAG>";
    
    # parse xml
    my $document = parse_xml($_);

    # if there is no parsing error do the validation
    if (defined $document)
    {
        # recursive call to validate each node (Element node)
        validate_node($document->getDocumentElement);

        # store the configuration tree
        $dom = $document->cloneNode(1);        

        # Avoid memory leaks
        $document->dispose;
    }
}


# Args: DOM::XML::Element
# Return: void
# Traverse recusively the DOM::XML::Element
# and verify attributes and their values
# If these are not compatible with those in 
# %xml_map then report and error.
sub validate_node
{
    # get current node
    my $node = shift;
    
    # get a NamedNodeMap of atributes corresponding to current node
    my $namedNodeMap = $node->getAttributes;

    # get list of attributes --- getValues is not standard in DOM Spec
    my $list = $namedNodeMap->getValues;
         
    # get length of list of attributes
    my $length = $list->getLength;        
    
    # validate each attribute
    for (my $i = 0; $i < $length; $i++)
    {
        # call validation function
        validate_attribute($list->item($i), $node->getTagName);
    }

    # get list of all child nodes, and their number
    $list = $node->getChildNodes;
    $length = $list->getLength;

    # validate each child - only Element
    for (my $i = 0; $i < $length; $i++)
    {
        # get the child node and its type
        my $child = $list->item($i);
        my $child_type = $child->getNodeType;

        # if the child type is Element then validate it
        if ($child_type == ELEMENT_NODE)
        {
            # recursive call
            validate_node($child);
        }
    }
}


# Args: DOM::XML::Attr, string (tag name for current cell)
# Return: void
# Reports two types of errors:
#    - invalid attribute given
#     - invalid value for attribute
sub validate_attribute
{
    # get attribute, its name and value
    my $attribute = shift;
    my $attr_name = $attribute->getName;
    my $attr_value = $attribute->getValue;
    
    # get cell name
    my $cell = shift;

    ######################################
    # report invalid attribute - section #
    ######################################

    # search for $attr_name in keys of %xml_attr map
    # which contains all valid K configuration attributes    
    my $valid = 0;
    for my $key (keys %xml_attr)
    {
        # set $valid if $attr_name is available
        $valid = 1 if ($key eq $attr_name);
    }

    # report error if $attr_name is not allowed in K configurations
    # print("Attribute $attr_name is not valid in configuration.\n") if !$valid;
    error_report($INVALID_ATTRIBUTE_ERROR, $attr_name, $cell) if !$valid;    

    # return if the attribute is not valid
    return if !$valid;

    ################################################
    # report invalid value for attribute - section #
    ################################################

    # get valid values for current attribute
    my $values = " " . $xml_attr{$attr_name} . " ";

    # report error if $attr_value is not a valid value 
    # for $attr_name attribute according to %xml_attr
    # print("Value |$attr_value| is not valid for attribute |$attr_name|.\nVALS:|$values|\n") if $values !~ /\s\Q$attr_value\E\s/;
    error_report($INVALID_VALUE_FOR_ATTRIBUTE_ERROR, $attr_name, $attr_value, $cell) if $values !~ /\s\Q$attr_value\E\s/;
}




##########################
# Error report - section #
##########################

# Args: error code [, other args specific for error code]
# Return: void
# Reports an error by adding an error message in @container
sub error_report
{
    # do something only if $session is started
    if ($session)
    {
        # get error type
        my $error = shift;

        # identify the $error type and generate specific
        # error messages which will be added to @container
        switch ($error)
        {
            # ... will be used for regular messages/unknown (future) errors.
            case ($ERROR)
                { 
                    # get message                                
                    my $msg = shift;

                    # generate error message
                    my $err_msg = generate_error("ERROR", $ERROR, $file, "unknown line", $msg);

                    # add error in @container
                    push(@container, $err_msg);
                }

            case ($INVALID_ATTRIBUTE_ERROR)
                { 
                    # receives as args the attribute name and cell name
                    my $attribute = shift;
                    my $cell = shift;
                
                    # get the cell line
                    my $line = get_cell_line($cell, $configuration) + $config_line;

                    # get available attributes
                    my @atts = keys %xml_attr;
                    my $attrs = "@atts";

                    # generate error message
                    my $err_msg = generate_error("ERROR", $INVALID_ATTRIBUTE_ERROR, $file, $config_line, "in configuration attribute \"$attribute\" is not allowed for cell <$cell> at line $line. You should try: $attrs");

                    # add error message to @container
                    push(@container, $err_msg);
                }

            case ($INVALID_VALUE_FOR_ATTRIBUTE_ERROR)
                { 
                    # receives as args the attribute name, its value and cell name
                    my $attribute = shift;
                    my $value = shift;
                    my $cell = shift;
                
                    # get the cell line
                    my $line = get_cell_line($cell, $configuration) + $config_line;

                    # get available values for $attribute
                    my $vals = $xml_attr{$attribute};

                    # generate error message
                    my $err_msg = generate_error("ERROR", $INVALID_VALUE_FOR_ATTRIBUTE_ERROR, $file, $config_line, "in configuration, attribute \"$attribute\" has an invalid value \"$value\" in cell <$cell> at line $line. The available values for \"$attribute\" are: $vals");            

                    # add error message to @container
                    push(@container, $err_msg);
                }
        
            case ($INVALID_XML)
                {
                    # receives as args the xml parser output
                    my $xml_err = shift;

                    # if the parser is not found or there are some missing 
                    # files, then throw the (native) error and exit
                    if ($xml_err =~ /compilation\s+failed/sg)
                    {
                        # print error message
                        print "$xml_err\n";
                
                        # exit
                        exit(1);
                    }

                    # format the $xml_err
                    $xml_err = format_xml_parser_output($xml_err);
    
                    # replace "tag" with "cell"
                    $xml_err =~ s/tag/cell/sg;

                    # insert the absolute line number
                    $xml_err =~ s!\s([0-9]+)$!{$config_line = $1 + $config_line;}" " . $config_line!sge;
                    $xml_err = generate_error("ERROR", $INVALID_XML, $file, $1 + $config_line, $xml_err);

                    # add $xml_err to @container
                    push(@container, $xml_err);    
                }        
        }
    }
}

# Args: TO DO
# Return: void
# Start a try-catch "session"
#     - report errors if $session is "open"
#    - reported errors will be stored in @container
sub try
{
    # Start a new session
    $session = 1;
}


# Args: void
# Return: void
# "Catch" all the exceptions stored in @container
# and print them on the screen
# Reset the session
sub catch
{
    # print all errors
    foreach(@container)
    {
        # print formatted
        print format_error($_);
    }    
    
    # clear the @container
    @container = ();

    # reset session
    $session = 0;
}

# Args: string = error message
# Return: formatted error message
# For message $err returns: "Error: $msg.\n"
sub format_error
{
    # return formatted error message
    return (shift) . ".\n";
}

# Args: xml parser error message
# Return: formatted error message
# For message $err returns: "Error: $msg.\n"
sub format_xml_parser_output
{
    # get the xml parsing error
    local $_ = shift;

    # extract only relevant data from the xml error
    # - error message
    # - line number
    my $xml_err = "";
    my $line = 0;
    # this is based on the error message returned by the
    # xml parser: error message at line number, ...
    if (/\s*(.*?)\s+at\s+line\s+(.*?),/sg)
    {
        $xml_err = $1;
        $line = $2;
    }    
    
    # return formatted error message
    # return "Error: $_ \n";
    return "configuration (@ line $config_line) cannot be parsed --> $xml_err at line $line";
}

# Args: cell name, configuration string
# Return: line number for cell in configuration
# Match the cell in the configuration and 
# count the lines before the match
sub  get_cell_line
{
    # get the cell and the configuration
    (my $cell,local $_) = (shift, shift);

    # match cell in configuration
    if (/<\s*$cell\s/sg)
    {    
        # count newlines in the string before matching cell
        return $` =~ tr/\n//;
    }

    # return 0 by default
    return 0;
}


# Args: void
# Return: void
# Creates a perl script which calls an xml parser
# and exits if there are errors
sub create_xml_parser
{
#    $path = File::Spec->rel2abs($path);

        # quote dots and array-like symbols in paths 
        $path =~ s/(@|\.)/\\($1)/sg;
    
    # the newly generated perl file
    # runs a xml parser which will detect 
    # (and die with some error message)
    # if the xml cannot be parsed
    my $content =
    "#!/usr/bin/perl
    use strict;    
    use warnings;
    use lib \"$path\";

    # imports
    use XML::DOM;


    # this script parses an XML and dies if there is any parsing error

    # get the xml argument
    my \$xml = \$ARGV[0];

    # create a new parser
    my \$parser = new XML::DOM::Parser();

    # create doc tree
    my \$doc = \$parser->parsefile(\$xml);";

    # save content in file
    open FILE, '>', $xml_parser;
    print FILE $content;
    close FILE;
}


# Args: void
# Return: void
# Deletes temporary files
sub clean_
{
    # delete $temporary
    unlink $temporary;

    # delete $xml_parser
    unlink $xml_parser;
}


# Args: hash map
# Return: void
# Display a hash map 
sub print_map
{
    # get hashmap
    my $map = shift;

    # print each pair
    while ( my ($key, $value) = each(%$map) ) 
    {
        print "$key => $value\n";
    }
}

# Args: void
# Return: a string which represents the cell label declarations
# Check each node of the xml tree and build the declaration for each label
sub get_cell_label_declarations
{
    # clear $temp_var content
    $temp_var = "";

    # visit
    &visitor($dom->getDocumentElement, \&get_cell_declaration) if (defined $dom);

    # remove K generated TAG
    $temp_var =~ s/op\s+\Q$TAG\E\s+:\s+\->\s+CellLabel//s;

#    print "TREE: " . $dom->toString . "\n\n";
#    print "VAR: $temp_var\n";

    # clear 
    return $temp_var;
}

# Args: DocumentElement
# Return: void
# Generate op for each cell; add metadata if there is any color 
# attribute for the current cell
sub get_cell_declaration
{
    # get the argument of type DocumentElement
    my $cell = shift;

    # get the cell name
    my $cellname = $cell->getTagName;

    # get the color attribute
    my $color = $cell->getAttribute("color");

    # append the declaration 
    $temp_var .= " op $cellname : -> CellLabel [metadata \"latex=(color: $color)\"]" if $color ne "";
    $temp_var .= " op $cellname : -> CellLabel" if $color eq "";
}

# Args: DocumentElement, a function
# Return: void
# This is a typical visitor function which receives
# a Document Element and apply a function on it.
sub visitor
{
    # the first parameter is a Document Element
    my $node = shift;

    # the second parameter is a function
    my $function = shift;

    # apply this function to the current node
    &$function($node);

    # recurse
    # get list of all child nodes, and their number
    my $list = $node->getChildNodes;
    my $length = $list->getLength;

    # visit each child - only Element
    for (my $i = 0; $i < $length; $i++)
    {
        # get the child node and its type
        my $child = $list->item($i);
        my $child_type = $child->getNodeType;

        # if the child type is Element then visit it
        if ($child_type == ELEMENT_NODE)
        {
            # recursive call
            visitor($child, $function);
        }
    }

}


# Args: Error type (WARNING/ERROR), error code, current file, error line, error message
# Return: string
# Format an error message
sub generate_error
{
    my $type = shift;
    my $code = shift;
    my $file = shift;
    my $line = shift;
    my $message = shift;

    return wrap("", "", "[$type][$code] in [$file] @ [$line]: [$message]\n");
}







##############################
# DOTS replacement in rules #
#############################

# contains cell types
my %cell_types_map = ();

# locally used
my @kmaude_keywords = qw(context rule macro eq ceq configuration op ops syntax kvar sort sorts subsort subsorts including kmod endkm mb);
my $kmaude_keywords_pattern = join("|",map("\\b$_\\b",@kmaude_keywords));

# K data types
my $types = "List|Map|Set|Bag|K";

sub build_map
{   
    local $_ = shift;
    
    if (defined)
    {
	# K configuration
	local $_ = "<$TAG>$_</$TAG>";
	
	# parse xml
	my $document = parse_xml($_);
	
	build_rec_map($document->getDocumentElement) if defined $document;
    }
}

sub build_rec_map
{
    # get element
    local $element = shift;

    my $cell = $element->getTagName;
#    print "Node: $cell\n";
    
    # get children
    my @children = $element->getChildNodes;

    # go recursively
    foreach (@children)
    {
        # text nodes are leaves => check cells type
        if ($_->getNodeType == TEXT_NODE)
        {
            # get content
            my $type = $_->toString;
            
            # clean spaces
            $type =~ s/^\s*//sg;
            $type =~ s/\s*$//sg;
            
            # register types if any
            if (($type ne "") and ($type =~ /^\.($types)$/sg or $type =~ /:($types)$/sg))
            {
                # print "\thas type $1\n";
                $cell_types_map{$cell} = $1;
            }
        }
        else
        {
            # go deep
            build_rec_map($_);
        }
    }
}

sub replace_dots
{
    local $_ = shift;
    my $return = $_;
    
    # build the types map
    if (/configuration\s+(.*?)\s+(?=$kmaude_keywords_pattern)/sg)
    {
        build_map($1) if defined $1;
    }
    
    # foreach rule
    while (/rule(.*?)(?=$kmaude_keywords_pattern)/sg)
    {
        my $rule = $1;
        my $temp_rule = $rule;
#        print "Rule: $rule\n";
        
        # check each typed cell and replace dots with its type
        while (my ($cell, $type) = each(%cell_types_map))
        {
#            print "\tCheck cell: $cell($type)\n";
            if ($rule =~ /(<$cell\_?>)(.*?)(<\_?\/$cell>)/sg)
            {
#                print "\t\tFound:$&\n"; 
                my $left = $1;
                my $right = $3;
                my $content = $2;
                my $temp = $&;
                my $tmp = $content;
                
#                print "\t\tcontent: |$content|\n";
                if ($tmp =~ /^(\s*)\.(\s*)$/sg)
                {
                    # basic case of dot <k>.</k>
                    $content = "$1.$type$2";
                }
                elsif ($tmp =~ /^(\s*)\.(\s*\=>.*)$/sg)
                {
                    # . => something
#                    print "\t\t\tcont1: $content\n";
                    $content =~ s/^(\s*)\.(\s*\=>.*)$/$1.$type$2/sg;
#                    print "\t\t\tcont1: $content\n";
                }
                elsif ($tmp =~ /^(.*?\=>\s*)\.(\s*)$/sg)
                {
                    # something => .
#                    print "\t\t\tcont2: $content\n";
                    $content =~ s/^(.*?\=>\s*)\.(\s*)$/$1.$type$2/sg;
#                    print "\t\t\tcont2: $content\n";
                }
                
                $rule =~ s/\Q$temp\E/$left$content$right/sg;
#                print "\t\tcontent: |$content|\n";
#                print "\t\trule: $rule\n";
            }
        }
        
#        print "New rule: $rule\n";
        $return =~ s/\Q$temp_rule\E/$rule/sg;
    }

    return $return;
}



1;
