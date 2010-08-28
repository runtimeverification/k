# !usr/bin/perl -w
use strict;
use warnings;
use File::Spec;
use File::Basename;
use File::Temp;

my $path = ".";

BEGIN {
    $path = (File::Basename::fileparse($0))[1];
}


use lib $path;
use Tree::Nary;

my $language_file_name = "?";
my $config_tree;
my $iteration_cells = {};
my $warnings = "";
my $warnings_file = "kompile_warnings" . fresh() . ".txt";
my $comment = join("|", (
    "---\\(.*?---\\)",                                                                                                            
    "---.*?\$",                                                                                                                   
    "\\*\\*\\*\\(.*?\\*\\*\\*\\)",                                                                                                
    "\\*\\*\\*.*?\$"                                                                                                              
));     
my $verbose = 0;
my @nodes = ();
my $current_line = 0;

# explicit call for debugging.
# syntax_common_check($ARGV[0]);

# remove "kompile_warnings.txt"
if (-e $warnings_file)
{
#	system("rm", "$warnings_file");
    unlink($warnings_file);
    print "Previous version of $warnings_file removed.\n" if $verbose;
}	

# start syntax checking.
sub syntax_common_check
{
    $language_file_name = (shift);

    if ($language_file_name !~ m/\.k|\.kmaude/)
    {
	if (-e "$language_file_name.k")
	{
	    $language_file_name .= ".k";
	}

	if (-e "$language_file_name.kmaude")
	{
	    $language_file_name .= ".kmaude";
	}
    }
    
#    print "LANG: $language_file_name.\n\n";
# exit(1);
    syntax_verification();
    
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
	warning(" - configuration definition is not correct. Unmatched cell <$1>");
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
	warning("(@ line $current_line) - in expression:\n$rule\nUnmatched cell <$1>.");
    }
    
    return $root;
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
	    warning("(@ line $current_line) - missing declarations of cells:$not_found_def in:\n$rule\nAre you sure cell <$node_data> should be closed?");
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
    
    # get a list o all nodes.
    find_all($node_data);

    if (scalar @nodes == 0)
    {
	warning("(@ line $current_line) - cell <" . $node_data . "> in: \n" . $rule . "\nis not defined in configuration.");
    }
    
    my $flag = 0;
    for my $config_node (@nodes)
    {
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
	    warning("(@ line $current_line) - cell <" . $node_data . "> in:\n" . $rule . "\nhas parent <" 
		. $parent_data ."> which is not defined in configuration.");
	}
	
	
	# check if $parent_node_config is ancestor for $config_node
	if (Tree::Nary->is_ancestor($parent_node_config, $config_node) == $Tree::Nary::TRUE
	    || Tree::Nary->is_ancestor($config_node, $parent_node_config) == $Tree::Nary::TRUE)
	{
	    $flag = 1;
	}	
    }
    
    if ($flag == 0)
    {
	warning("(@ line $current_line) - cell structure in:\n$rule \nis not a substructure in configuration.");
    }   
    
    # clear array
    @nodes = ();
    
    return $Tree::Nary::FALSE;
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
    my $source = $_;
    
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
	warning("INFO: File $language_file_name does not contain configuration definition.\n") if $verbose;
	return;
    }
    
    # learn configuration
    $config_tree = append_rec_tree($lines, "super-node");
        
    # verify each rule for errors
    my $no = 0;
    while ($source =~ m/(rule|eq|macro)(\s+)(.*?)(\s|\n)+(?=(rule|op|ops|eq|---|context|subsort|subsorts|configuration|syntax|macro|endkm)(\s|\n)+)/sg)
    {
	my $match_line = $-[0];
	my $original_rule = $3;
	my $temp = $3;
	my $expr_type = $1;

	$temp =~ s/top\(.*?\)//;
	
	# get the line number
	$current_line = find_line($source, $match_line);

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


sub warning
{
    $warnings .= "WARNING" . (shift) . "\n";
}

sub write_warnings
{
    if (length($warnings) > 1)
    {
	my $display_warnings = "";
	my $i = -1;
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
	print "...\nCheck $warnings_file for the remaining warnings\n" if $i >= 10;             
    }
}

sub find_line
{
    my ($text, $end) = (shift, shift);
    
    my $lines = substr $text, 0, $end;
    
    my $l_no = 1;
    while($lines =~ m/\n/g)
    {
	$l_no++;
    }
    
    return $l_no;
}

sub find_all
{
    my $node_name = shift;
    
    # reset
    @nodes = ();
    
    my $s = "";
    Tree::Nary->traverse($config_tree, $Tree::Nary::PRE_ORDER,
	$Tree::Nary::TRAVERSE_ALL, -1, \&show, \$node_name);
}

sub show()
{
    # get current node and ref to arguments
    my ($node, $ref) = (shift, shift);
  
    # get arguments reference
    my $p = $ref;
    my $n;
    
    # if no reference to arguments defined, no node is known
    if(defined($p)) 
    {
		$n = $$p;
    } 

    # add node in list if found
    if ($node->{data} eq $n)
    {
	push(@nodes, $node);
    }
    
    return $Tree::Nary::FALSE;
}

sub setVerbose()
{
    $verbose = 1;
}

sub printErrorFromOut()
{
    local $/=undef; open FILE,"<", "kompile_out.txt" or print ""; local $_ = <FILE>; close FILE;
    my $content = $_;
    close FILE;
    my $out = "";
    if ($content =~ m/error(.*?)\n/isg)
    {
	$out = "Error $1\n";
    }
    
    $out;
}

sub fresh
{
    my $f = File::Temp->new();
    $f = substr $f, 5;
    $f;
}

1;
