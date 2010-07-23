# !usr/bin/perl -w
use strict;
use warnings;

my $path = ".";
BEGIN {
	use Cwd 'abs_path';
	$path = abs_path($0);
	$path =~ s/(kompile\.pl)|(common_functions\n.pl)//;
}

use lib $path;
use Tree::Nary;

my $language_file_name = "?";
my $config_tree;
my $iteration_cells = {};
my $warnings = "";
my $warnings_file = "kompile_warnings.txt";
my $comment = join("|", (
    "---\\(.*?---\\)",                                                                                                            
    "---.*?\$",                                                                                                                   
    "\\*\\*\\*\\(.*?\\*\\*\\*\\)",                                                                                                
    "\\*\\*\\*.*?\$"                                                                                                              
));     

# explicit call for debugging.
# syntax_common_check($ARGV[0]);

# start syntax checking.
sub syntax_common_check
{
    $language_file_name = (shift);
    
    if ($language_file_name =~ /(?:.k|.kmaude)$/)
    {	
	syntax_verification();
    }
    
    write_warnings();
}


# build recursively a configuration tree
sub append_rec_tree
{
    my ($temp_cfg, $node_name) = (shift, shift);

    # create the new node
    my $root = new Tree::Nary->new($node_name);
    
    # append to the created node its children
    while ($temp_cfg =~ m/<\s*(.+?)\s*>\s*(.+?)\s*<\s*\/\s*\1>\s*/sg)
    {
	my $cell_name = $1;
	my $cell_content = $2;
	
	# mark each cell* - iterated cells
	if ($cell_name =~ m/\*/)
	{
	    # eliminate * - iteration
	    $cell_name =~ s/\*//;
	    $iteration_cells->{$cell_name} = 'iterated';
	}
	

	my $node = &append_rec_tree($cell_content, $cell_name);
	Tree::Nary->append($root, $node);
    }
    
    # remove all children (from text) in order to find 
    # unmatched cells
    $temp_cfg =~ s/<\s*(.+?)\s*>\s*(.+?)\s*<\s*\/\s*\1>\s*//sg;  
    
    # find unmatched cells and report them.
    if ($temp_cfg =~ m/.*<(.+?)>.*/s)
      {
	  warning("configuration definition is not correct. Unmatched cell <$1>");
      }
    
    return $root;
}                    

# build recursively a rule tree
# mark the closed nodes
sub append_rec_tree_for_rule
{
    my ($temp_cfg, $node_name, $rule) = (shift, shift, shift);
    
    # create the new node
    my $root = new Tree::Nary->new($node_name);
    
    # append to the created node its children
    my $node;

    while ($temp_cfg =~ m/<\s*(.+?)(_?)\s*>\s*(.+?)\s*<\s*(_?)\/\s*\1\s*>\s*/sg)
    {
	if ($2 ne "_" && $4 ne "_")
	{
	    $node = &append_rec_tree_for_rule($3, $1 . ";;;;;closed", $rule);
	}
	else
	{
	    $node = &append_rec_tree_for_rule($3, $1, $rule);
	}
	
	Tree::Nary->append($root, $node);
    }
    
    # remove all children (from text) in order to find 
    # unmatched cells
    while ($temp_cfg =~ m/<\s*(.+?)(_?)\s*>\s*(.+?)\s*<\s*(_?)\/\s*\1\s*>\s*/sg)
      {
	  $temp_cfg =~ s/<\s*(.+?)(_?)\s*>\s*(.+?)\s*<\s*(_?)\/\s*\1\s*>\s*//sg;
      }  
    
    # find unmatched cells and report them.
    if ($temp_cfg =~ m/.*<([^\'=]+?)>.*/s)
      {
	  warning("in expression:\n$rule\nUnmatched cell <$1>.");
      }
    
    return $root;
}                    

# verify syntax by learning configuration
sub syntax_verification
{
    # Slurp all $file into $_;
    local $/=undef; open FILE,"<",$language_file_name or die "Cannot open $language_file_name\n"; local $_ = <FILE>; close FILE;

    # Getting rid of comments, maintaining the line numbers of the remaining code
    s/($comment)/
    {
	local $_=$1;
	s!\S!!gs;
	$_;
    }/gsme;

    my $lines = $_;
    
    # keep source
    my $source = $lines;
    
    ###########################################
    # parse and learn configuration structure #
    #                                         #
    # - the configuration structure is stored #
    # in an n-ary tree.                       #
    ###########################################

    # extract configuration string from .kmaude file
    if ($lines =~ m/configuration\s*(.+?)(\s|\n)+(?=(rule|op|ops|eq|---|context|subsort|subsorts|configuration|syntax|macro|endkm)(\s|\n)+)/s)
    {
	$lines = $1;
    }
    else
    {
#	print "INFO: File $language_file_name does not contain configuration definition.\n";
	return;
    }
    
    # learn configuration
    $config_tree = append_rec_tree($lines, "super-node");    
   
    # verify each rule for errors
    my $no = 0;
    while ($source =~ m/(rule|eq|macro)(\s+)(.*?)(\s|\n)+(?=(rule|op|ops|eq|---|context|subsort|subsorts|configuration|syntax|macro|endkm)(\s|\n)+)/sg)
    {
	my $original_rule = $3;
	# print "Matched: $1$2$3$4\n";
	my $temp = $3;
	my $expr_type = $1;
	
	$temp =~ s/top\(.*?\)//;
	
	# eliminate rules that not contain cell definitions
	# also eliminate ambigous rules int < int => int
	if ($temp =~ m/(.*?)<.*?[^=]>/)
	{
	    # build rule tree
	    my $exp_tree = append_rec_tree_for_rule($temp, "super-node", "rule $original_rule");
	    
	    # $string will be used as DATA parameter for traverse function
	    my $string = $expr_type . " " . $original_rule;

	    # check if rule tree tree ~ configuration tree
	    Tree::Nary->traverse($exp_tree, $Tree::Nary::PRE_ORDER,
		$Tree::Nary::TRAVERSE_ALL, -1, \&validate_node, \$string);

	    # check closed/open cells
	    Tree::Nary->traverse($exp_tree, $Tree::Nary::PRE_ORDER,
		$Tree::Nary::TRAVERSE_ALL, -1, \&validate_open_cells, \$string);
	}
	
	# process top(something)-like expressions
	while ($original_rule =~ m/top\s*\((.*?)\)/sg)
	{
	    my $top_content = $1;
	    if ($top_content =~ m/(.*?)<.*?[^=]>/)
	    {
		# build "top" inside tree
		my $exp_tree = append_rec_tree_for_rule($top_content, "super-node",  "rule $original_rule");
	    
		# $string will be used as DATA parameter for traverse function
		my $string = "top expression: $expr_type  $original_rule";
		
		# check if rule tree tree ~ configuration tree
		Tree::Nary->traverse($exp_tree, $Tree::Nary::PRE_ORDER,
		$Tree::Nary::TRAVERSE_ALL, -1, \&validate_node, \$string);
		
		# check closed/open cells
		Tree::Nary->traverse($exp_tree, $Tree::Nary::PRE_ORDER,
		$Tree::Nary::TRAVERSE_ALL, -1, \&validate_open_cells, \$string);
	    }   
	}
    }
}

# sub checks if the substructures determined by closed cells
# are also substructures in the configuration definition
sub validate_open_cells()
{
    # get current node and ref to arguments
    my ($node, $ref) = (shift, shift);
    
    # keep missing cells
    my $not_found_def = "";
    
    # ignore default root
    if ($node->{data} eq "super-node")
      {
	  return $Tree::Nary::FALSE;
      }
    
    # get arguments reference
    my $p = $ref;
    my $rule;
    
    # if no reference to arguments defined, the rule is unknown
    if(defined($p)) 
    {
	$rule = $$p;
    } 
    else 
    {
	$rule = "cannot identify rule!";;
    }

    # only for closed cells
    if ( $node->{data} =~ m/;;;;;closed/sg)
    {
	# get the coresponding node for $node in configuration tree
	my $node_data = $node->{data};
	# remove closed marker
	$node_data =~ s/;;;;;closed//;
	my $config_node = Tree::Nary->find($config_tree, $Tree::Nary::PRE_ORDER, 
	    $Tree::Nary::TRAVERSE_ALL, $node_data);
	
	
	# traverse childrens and check if they correspond to configuration definition
	my $no_of_childrens = Tree::Nary->n_children($config_node);
	my $i;
	for ($i = 0; $i < $no_of_childrens; $i++)
	{
	    # get node i name
	    my $child_data = Tree::Nary->nth_child($config_node, $i)->{data};

	    if (!defined($iteration_cells->{$child_data}) || ($iteration_cells->{$child_data} ne 'iterated'))
	    {
		my $bool1 = Tree::Nary->find($node, $Tree::Nary::PRE_ORDER, 
		    $Tree::Nary::TRAVERSE_ALL, $child_data) || $Tree::Nary::FALSE;
		my $bool2 = Tree::Nary->find($node, $Tree::Nary::PRE_ORDER, 
		    $Tree::Nary::TRAVERSE_ALL, $child_data . ";;;;;closed") || $Tree::Nary::FALSE;
		
		# if the child is not found then add it in the $not_found_def
		if (($Tree::Nary::FALSE == $bool1) && ($Tree::Nary::FALSE == $bool2))
		{
		    $not_found_def .= " <$child_data>";
		}
	    }
	}
	
	# if there are less children in rule tree than in the configuration tree print warning message
	if ($not_found_def ne "")
	{
	    warning("missing declarations of cells:$not_found_def in:\n$rule\nAre you sure cell <$node_data> should be closed?");
	}
    }
 
    return $Tree::Nary::FALSE;
}

# sub checks if there is a morphism between rule tree and configuration tree
sub validate_node()
{
    # get current node and ref to arguments
    my ($node, $ref) = (shift, shift);
    
    # ignore default root
    if ($node->{data} eq "super-node")
      {
	  return $Tree::Nary::FALSE;
      }
    
    # get arguments reference
    my $p = $ref;
    my $rule;
    
    # if no reference to arguments defined, no rule is known
    if(defined($p)) 
    {
	$rule = $$p;
    } 
    else 
    {
	$rule = "cannot identify rule!";;
    }
    
    # get the coresponding for $node in configuration
    my $node_data = $node->{data};
    
    # remove "closed" markers
    $node_data =~ s/;;;;;closed//;
    
    my $config_node = Tree::Nary->find($config_tree, $Tree::Nary::PRE_ORDER, 
	$Tree::Nary::TRAVERSE_ALL, $node_data);
    
    # if node not found in configuration: exit
    if (!defined($config_node))
    {
	warning("cell <" . $node_data . "> in: \n" . $rule . "\nis not defined in configuration.");
    }
    
    # get the parent for $node in rule
    my $parent_node_rule = $node->{parent};
    my $parent_data = $parent_node_rule->{data};
    $parent_data =~ s/;;;;;closed//;
   
    # get the coresponding for $parent_node_rule in configuration
    my $parent_node_config = Tree::Nary->find($config_tree, $Tree::Nary::PRE_ORDER, 
	$Tree::Nary::TRAVERSE_ALL, $parent_data);

    # if undefined parent node in configuration: warning
    if (!defined($parent_node_config))
    {
	warning("cell <" . $node_data . "> in:\n" . $rule . "\nhas parent <" 
	  . $parent_data ."> which is not defined in configuration.");
    }
    
    
    # check if $parent_node_config is ancestor for $config_node
    if (Tree::Nary->is_ancestor($parent_node_config, $config_node) == $Tree::Nary::FALSE
	&& Tree::Nary->is_ancestor($config_node, $parent_node_config) == $Tree::Nary::FALSE)
    {
	warning("cell structure in:\n$rule \nis not a substructure in configuration.");
    }	
    
    return $Tree::Nary::FALSE;
}

sub warning
{
#    print "WARNING: " . (shift) . "\n";
    $warnings .= "WARNING: " . (shift) . "\n";
}

sub write_warnings
{
    if (length($warnings) > 1)
    {
	my $display_warnings = "";
	my $i = 0;
	while ($warnings =~ m/(.*?)\n/g)
	{
	    if ($i < 10)
	    {
		$display_warnings .= "$1\n";
	    }
	     
	    $i++;
	}

	open FILE, ">", $warnings_file or die "Cannot open/create warnings file.\n";
	print FILE $warnings;
	close $warnings;
	print $display_warnings;
	print "...\nCheck $warnings_file for the remaining warnings\n" if $i > 10;             
    }
}
1;