#!/usr/bin/env perl -w
use strict;
use warnings;
use File::Spec;
use File::Basename;
use File::Temp qw / tempfile /;
use Digest::MD5 qw(md5 md5_hex md5_base64);

use Text::Wrap;
$Text::Wrap::columns = 75;

our @checksum_files; # used in checksumming kompile program to detect version changes
our $preamble;
my $path = ".";

BEGIN {
    $path = (File::Basename::fileparse($0))[1];
}


use lib $path;
use Regexp::Common;
use Tree::Nary;

my $tab1 = "";
my $tab2 = "";

my $k_base =  File::Spec->catfile((File::Basename::fileparse($0))[1], "..");
my $maude = "maude";
my $language_file_name = "?";
my $config_tree;
my $iteration_cells = {};
my $warnings = "";
my $warnings_file = fresh("kompile_warnings", ".txt");
# my $comment = join("|", (
#        "\\/\\/.*?\n",
#        "\\/\\*.*?\\*\\/",
#		"---\\(.*?---\\)",
#		"---.*?\$",
#		"\\*\\*\\*\\(.*?\\*\\*\\*\\)",
#		"\\*\\*\\*.*?\$"
# ));

my $comment = join("|", (
    "\\/\\/.*?\n",
    "\\/\\*.*?\\*\\/",
    "---\\(.*?---\\)",
    "---.*?\n",
    "\\*\\*\\*\\(.*?\\*\\*\\*\\)",
    "\\*\\*\\*.*?\n"
));    

my $string_pattern = "\(?<![^\\\\]\\\\\)\".*?\(?<![^\\\\]\\\\\)\"";
my $latex_comment = join("|", (
        "\\/\\/@(.*?)(?=\n)",
        "\\/\\*@(.*?)\\*\\/",	
));

my $TAB = "    ";
     
my $verbose = 0;
my @nodes = ();
my $current_line = 0;

my $inclusionFileTree;
my $declaredKLabels = "";

# Top level patterns
my $top_level_pattern = join("|", (
                    "kmod(?:.*?)endkm",
                    "mod(?:.*?)endm",
                    "fmod(?:.*?)endfm",
                    "set\\s.*?\$",
                    "(?:in|load|require)\\s+\\S+"
    ));

my @kmaude_keywords = qw(context rule define macro eq ceq configuration op ops syntax declare kvar sort sorts subsort subsorts including kmod endkm mb tags);
my $kmaude_keywords_pattern = join("|",map("\\b$_\\b",@kmaude_keywords));
our $ksort = '#?[A-Z][A-Za-z0-9\`\+\?\!#]*(?:\{#?[A-Z][A-Za-z0-9\`\+\?\!]*(\,".*?")?\})?';

my $parentheses = "\Q{}[]()\E";
my $maude_backquoted = "(?:`\\(|`\\)|`\\{|`\\}|`\\[|`\\]|`\\,|_|[^$parentheses\\s\\,\\`])*";

# Pattern matched by K variables
my $klabel_body = "$maude_backquoted\_$maude_backquoted";
my $klabel = "'$klabel_body(?:[$parentheses\\s\\,])|$klabel_body(?=\\()";
my $kvar  = "[A-Za-z][A-Za-z0-9]*";

my $k_sorts = ":Bag:BagItem:#Bool:CellLabel:CellKey:CellAttribute:#Char:#Int:K:KAssignments:KHybridLabel:KLabel:KResult:KResultLabel:KSentence:List:ListItem:List{KResult}:List{K}:Map:MapItem:#Nat:NeBag:NeK:NeList:NeList{KResult}:NeList{K}:NeMap:NeSet:#NzInt:#NzNat:Set:SetItem:#String:#Zero";

my $non_k_sorts = "Bag|BagItem|CellLabel|CellKey|CellAttribute|KAssignments|KHybridLabel|KLabel|KResultLabel|KSentence|List|ListItem|List{KResult}|List{K}|Map|MapItem|NeBag|NeList|NeList{KResult}|NeList{K}|NeMap|NeSet|Set|SetItem";


# parametrize break
my $latex_break = quotemeta("<br/>");



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
# now, when the xml parser for configurations is available this function is 
# renamed into validate_node
sub validate_node_()
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

	# latex stuff <br/> or other marker is frozen here
	s/($latex_break)/LATEX_BREAK)/sg;

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
    if ($lines =~ m/(?<!mb)\s+configuration\s*(.+?)(\s|\n)+(?=(rule|op|ops|eq|---|context|subsort|subsorts|configuration|syntax|macro|endkm)(\s|\n)+)/s)
    {
	$lines = $1;
    }
    else
    {
	warning("INFO: File $language_file_name does not contain configuration definition.\n") if $verbose;
	return;
    }

#	print "LINES: $lines\n";

    # learn configuration
    $config_tree = append_rec_tree($lines, "super-node");
        
    # verify each rule for errors
    my $no = 0;
    while ($source =~ m/(rule|macro)(\s+)(.*?)(\s|\n)+(?=(rule|op|ops|eq|---|context|subsort|subsorts|configuration|syntax|macro|endkm)(\s|\n)+)/sg)
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
	print wrap("", "", $display_warnings . " ...\nCheck $warnings_file for the remaining warnings\n") if $i >= 10;
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
    if (-e $warnings_file)
    {
	local $/=undef; open FILE,"<", $warnings_file or print ""; local $_ = <FILE>; close FILE;
    
	if (/error(.*?)\n/isg)
	{
	    wrap("", "", "Error $1");
	}
    }
    else 
    {
	"";
    }
}
# generate fresh names for temp files
sub fresh
{
    my ($prefix, $suffix) = (shift, shift);
    my ($fh, $filename) = tempfile($prefix . "XXXXXXXXXX", SUFFIX => $suffix);
    $filename;
}



# deletes all temporary files
sub erase_temp
{
    opendir(DIR, ".");
    my @files = grep(/^(kompile_in|kompile_out|kompile_err|kompile_warnings|kompile_tmp)/,readdir(DIR));
    closedir(DIR);
    
    # print "Files removed: @files\n";
    
    foreach my $file (@files)
    {
	unlink($file);
    }
}

sub get_full_name
{
    my $file = (shift);
    if ($file eq "")
    {
	return $file;
    }
        
#    $file =~ s/^\.\///;

    # If $file has extension .k, .kmaude, .m or .maude then tests if $file exists and errors if not
    
    if ($file =~ /\.(k?(maude)?|m)$/) {
	if (! -e $file) {
#		print("File $file does not exist\n");
		print wrap("", "", generate_error("ERROR", 1, $file, "unknown line", "file $file does not exist"));
		exit(1);
	}
	return $file;
    }
    # If $file does not have the extension .k, .kmaude, or .maude then
    else {
	# Add extension .k if $file.k exists
	if (-e "$file.k") {
	    $file .= ".k";
	}
	# If not, then add extension .kmaude if $file.kmaude exists
	elsif (-e "$file.kmaude") {
	    $file .= ".kmaude";
	}
	# If not, then add extension .maude if $file.maude exists
	elsif (-e "$file.maude") {
	    $file .= ".maude";
	}
	# If not, then add extension .maude if $file.maude exists
	elsif (-e "$file.m") {
	    $file .= ".m";
	}
	# Otherwise error: we only allow files with extensions .k, .kmaude or .maude
	else {
#		print("Neither of $file.k, $file.kmaude, or $file.maude exist\n");
		print wrap("", "", generate_error("ERROR", 1, "$file.k", "unknown line", "Neither of $file.k, $file.kmaude, or $file.maude exist"));
		exit(1);
	}
    }
    return $file;
}


sub get_full_name_custom
{
    my $file = (shift);
    if ($file eq "")
    {
	return $file;
    }


    # If $file has extension .k, .kmaude, .m or .maude then tests if $file exists and errors if not
    
    if ($file =~ /\.(k?(maude)?|m)$/) {
	if (! -e $file) {
		return ""; # silently ignore
	}
	return $file;
    }
    # If $file does not have the extension .k, .kmaude, or .maude then
    else {
	# Add extension .k if $file.k exists
	if (-e "$file.k") {
	    $file .= ".k";
	}
	# If not, then add extension .kmaude if $file.kmaude exists
	elsif (-e "$file.kmaude") {
	    $file .= ".kmaude";
	}
	# If not, then add extension .maude if $file.maude exists
	elsif (-e "$file.maude") {
	    $file .= ".maude";
	}
	# If not, then add extension .maude if $file.maude exists
	elsif (-e "$file.m") {
	    $file .= ".m";
	}
	# Otherwise error: we only allow files with extensions .k, .kmaude or .maude
	else {
		return ""; # silently ignore
	}
    }
    return $file;
}
sub appendFileInTree
{
    my ($child, $parent) = (shift, shift);
        
    $child = get_full_name($child);
    $parent = get_full_name($parent);

    if ($parent eq "")
    {
	# root node
        $inclusionFileTree = new Tree::Nary->new($child);
#	print "Root: " . $inclusionFileTree-> . " \n\n"
    } 
    else
    {
	# new leaf
	my $node = Tree::Nary->new($child);
	my $parent = Tree::Nary->find($inclusionFileTree, $Tree::Nary::PRE_ORDER, 
	    $Tree::Nary::TRAVERSE_ALL, $parent);
	Tree::Nary->append($parent, $node);
	
#	print "Parent: " . $parent->{data} . "  child: " . $node->{data} . "\n\n";
    }    
}

sub display_node()
{
    # get current node and ref to arguments
    my $node = (shift);
    print $node->{data} . "\n";
    return $Tree::Nary::FALSE;
}

sub recurseIntoFiles
{
    my $file = get_full_name(shift);
    if ($file =~ m/(k\-prelude|pl\-builtins|shared)/)
    {
		return;
    }
    
    local $/=undef; open FILE,"<",$file or die "Cannot open $file\n"; local $_ = <FILE>; close FILE;
      
    s/($comment)/
    {
	local $_=$1;
	s!\S!!gs;
	$_;
    }/gsme;
    
    while ( s/^(\s*)($top_level_pattern)(\s*)//sm ) 
    {
		(my $before, local $_, my $after) = ($1,$2,$3);
		    if ( m!^kmod\s+(\S+)! ) {
			$declaredKLabels .= " " . getDeclaredKLabelList($_);
		}
		elsif ( m!^(?:in|load|require)\s+(\S+)! ) 
		{
				my $in = maudify($1, $file);
				my $v_node = Tree::Nary->find($inclusionFileTree, $Tree::Nary::PRE_ORDER, 
				$Tree::Nary::TRAVERSE_ALL, get_full_name($in));
				if (!$v_node)
				{
					appendFileInTree($in,$file);
					recurseIntoFiles($in);
				}
#			    printTree();
		}
    }
}

sub printTree
{
    my $inclusionFileTree = shift;
    print "=======Tree========\n";
    Tree::Nary->traverse($inclusionFileTree,, $Tree::Nary::PRE_ORDER,
	$Tree::Nary::TRAVERSE_ALL, -1, \&display_node);
    print "\n=======End=======\n";
}

sub getDeclaredKLabelList
{
    if (/(?:syntax\s+KLabel\s+::=)(.*?\S)\s*(?:$kmaude_keywords_pattern)/s)
    {
	my $list = $1;
	$list =~ s/(\[.*?\]|\n|\|)//g;
#	$list =~ s/(\(.*?\)|\n|\|)//g;
	$list =~ s/\s+/ /g;
	return " $list ";
    }
    
    return "";
}

sub getDeclLabels
{
    return $declaredKLabels;
}

sub isDeclaredKLabel
{
    my $label = (shift);
    if ($declaredKLabels =~ / $label /s)
    {
	return 0;
    }
    
    return 1;
}

sub getKLabelDeclarations
{
  my $mod = (shift);
  my $labels = "";
  my $special_perl_chars  = "$parentheses\Q\\^|*+?.\$\E";


  # consider each statement
  while ($mod =~ m/(rule|macro|context|eq|configuration)(.*?)(?=$kmaude_keywords_pattern)/sg)
  {
    my $statement = $2;

    # extract KLabels from current statement
    # Explaining regexp (^|\s|(?<!`)[\(\)\{\}\[\],])([']([^`\(\)\{\}\[\],\s]*(`[^`])?)*)(?=($|[\(\)\{\}\[\],\s]))
    # First part:  (^|\s|(?<!`)[\(\)\{\}\[\],])  describes what can be before a KLabel
    # before a KLabel we can either have the beginning of the string,
    # a space, or one of the (nonescaped) characters { } ( ) [ ] ,
    # note that we use negative lookahead for ` so that only one char is consumed for 
    # the prefix
    # Second part: ([']([^`\(\)\{\}\[\],\s]*(`[^`\s])?)*)  describes the KLabel itself
    # it must start with '  then it has some chars distinct from ` ( ) { } [ ] , \s
    # and then it can have a ` followed by any (non-space) char, and, if so, iterate
    # Final part: (?=($|[\(\)\{\}\[\],\s])  describes what ends a KLabel
    # since we know that the KLabel cannot end with ` we need to look ahead and check 
    # that the following character is either end of line, or one of the separators.
    while($statement =~ m/(^|\s|(?<!`)[\(\)\{\}\[\],])([']([^`\(\)\{\}\[\],\s]*(`[^`])?)*)(?=($|[\(\)\{\}\[\],\s]))/sg)
    {

      my $candidate = "$2";
      (my $token_pattern = $candidate) =~ s/([$special_perl_chars])/\\$1/g;

      if ($declaredKLabels =~ m/ $token_pattern /s)
      {
        # label cannot be declared if it is already declared
      }
      else
      {	
        if ($labels =~ m/$token_pattern /s)
        {
          # candidate is already in labels list
        }
        else
        {
          $labels .= "$candidate ";
        }
      }
    }
  }

  # patch for shared.k 
  return $labels;

  if ($labels =~ m/\S\s+\S/)
  {
    $labels = "ops $labels";
  }
  elsif ($labels =~ m/\S/) 
  {
    $labels = "op $labels";	
  }
  else 
  {
    return "";
  }

  # print "$labels : -> KLabel [metadata \"generated label\"] ";
  return "$labels : -> KLabel [metadata \"generated-label=()\"] . ";
}

my $flatten = "";
my $include = "";
sub flattening
{
	#~ get file name
	my $file = (shift);

	#~ get the flat content
	recurseFlat($inclusionFileTree);
	my $out = "$include\n$flatten\n";
	
	#~ prepare for kompile
	#~ my $cap = uc($file);
	#~ $out =~ s/$cap/$cap-FLAT/g;
		
	#~ print to file-flat.k the result
	my $output_file = "$file-flat.k";
	open FILE,">",$output_file or die "Cannot create $output_file\n";
	print FILE $out;
	close FILE;
	
#	print "$include\n $flatten\n";
}


sub recurseFlat
{
	my $current_node = (shift);
	my $file = get_full_name($current_node->{data});
	my $out = "";
	
	if ($file =~ /\.k(maude)?$/)
	{
		#~ go to leaves first
		Tree::Nary->children_foreach($current_node, $Tree::Nary::TRAVERSE_ALL, \&recurseFlat);
	}
	else {return;}

	local $/=undef; open FILE,"<",$file or die "Cannot open $file\n"; local $_ = <FILE>; close FILE;

	$out = "\n--------- File: $file -----------------\n\n";
	while ( s/^(\s*)($top_level_pattern)(\s*)//sm ) 
	{
		(my $before, local $_, my $after) = ($1,$2,$3);
		if ( m!^(?:in|load)\s+(\S+)! ) 
		{
			#~ do nothing;
			my $line = $_;
			my $decl = get_full_name($1);
			if ($decl =~ /\.m(aude)?$/)
			{
				$include .= "$line\n";
			}
		}
		else 
		{
			$out .= "$before$_$after";
		}
	}
	
	$flatten .= $out;
}

###################
# require stuff   #
###################

my @imports = ();

sub store_import
{
	push(@imports, shift);
}

# determine whether a file can include other files
sub required
{
	my $req_file = shift;
	
	# $req_file = basename($req_file);

	if (defined $req_file && scalar @imports > 0)
	{
		foreach(@imports)
		{
			return 0 if (defined $_ && /\Q$req_file\E/);
		}
	}

	return 1;
}

#####################
# end require       #
#####################

# builds a configuration tree without considering ? or * or + in cells
sub build_config_tree
{
    my ($temp_cfg, $node_name) = (shift, shift);

    # get rid of * ? +
    $node_name =~ s/\s*\*\s*//g;
    $node_name =~ s/\s*\?\s*//g;
    $node_name =~ s/\s*\+\s*//g;

    # create the new node
    my $root = new Tree::Nary->new($node_name);
    
    # append to the created node its children
    while ($temp_cfg =~ m/<\s*(.+?)\s*_?\s*>\s*(.+?)\s*<\s*_?\s*\/\s*\1>\s*/sg)
    {
	my $cell_name = $1;
	my $cell_content = $2;

	my $node = &build_config_tree($cell_content, $cell_name);
	Tree::Nary->append($root, $node);
    }

    # keep content too
    if ($temp_cfg !~ m/<\s*(.+?)\s*_?\s*>\s*(.+?)\s*<\s*_?\s*\/\s*\1>\s*/sg)
    {	
	my $node = new Tree::Nary->new($temp_cfg);
	Tree::Nary->append($root, $node);
    }

    
    # remove all children (from text) in order to find
    # unmatched cells
    $temp_cfg =~ s/<\s*(.+?)\s*_?\s*>\s*(.+?)\s*<\s*_?\s*\/\s*\1>\s*//sg;  
    
    return $root;
}                    

###############################################
#   replacing dots                            #
###############################################

my $rule_leafs = "";
my $config_leafs = "";
my $configuration_tree;
my $cfgNode;
my $configSubtree;

sub replace_dots_
{
    local $_ = shift;
    
    my $rule;
    my $rule1;
    my $temp_rule;
    my $rule_tree; 
    my $nn;
    my $chno;
    my $tmp_cfg;

#    print "GOT: $_\n";
    
    my $config = "";
    
# Getting rid of comments, maintaining the line numbers of the remaining code
    s/($comment)/
    {
	local $_=$1;
	s!\S!!gs;
	$_;
    }/gsme;
    
    my $ret = $_;
    
    # get configuration
    if (/configuration\s+(<(.*?)>.*?<\/\2>)/gs) { $config = $1; }
#    print "Config: $config\n";
    
    # build configuration tree
    $configuration_tree = build_config_tree($config, "super-node");

#    printTree($configuration_tree);

    # consider each rule
    while (/(rule.*?(?=($kmaude_keywords_pattern)))/gs)
    {
	# keep the rule twice; $rule will be modified.
	$rule = $1;
	$rule1 = $rule;
	
	# get the rule tree
	$rule_tree = build_config_tree($rule, "super-rule-node");
	
	# get no of nodes
	$nn = Tree::Nary->n_nodes($rule_tree, $Tree::Nary::TRAVERSE_ALL);
	
	# consider only the cases when the rule contains at least one cell
	# super-node and rule text without cells ignored
	if ($nn > 2)
	{
#	    print "Rule: $rule\nTREE:\n";
#	    printTree($rule_tree);
	    
	    # iterate through rule tree leafs
	    $chno = Tree::Nary->n_children($rule_tree);
	    
	    my $i = 0;
	    for ($i = 0; $i < $chno; $i++)
	    {
            $temp_rule = Tree::Nary->nth_child($rule_tree, $i);
#            print "SEARCHING: " . $temp_rule->{data} . "\n in CONFIGURATION: ";
#            printTree($configuration_tree);
            # get corresponding subtree from configuration tree
            $tmp_cfg = Tree::Nary->find($configuration_tree, $Tree::Nary::PRE_ORDER, $Tree::Nary::TRAVERSE_ALL, $temp_rule->{data});
            $configSubtree = $tmp_cfg;
            
            # assign to each leaf inside rule tree its corresponding leaf from configuration tree
#            print "TREE CFG:";
#            printTree($tmp_cfg);
            if (Tree::Nary->n_nodes($tmp_cfg, $Tree::Nary::TRAVERSE_ALL) > 0)  
            {
                Tree::Nary->traverse($temp_rule, $Tree::Nary::PRE_ORDER, $Tree::Nary::TRAVERSE_ALL, -1, \&collect_rule_leaf);
            }
            else
            {
                # reset "registers"
                $rule_leafs = "";
                $config_leafs = "";
            }
	    }
	    
	    # if there is something to change ....
	    if ($rule_leafs ne "" && $config_leafs ne "")
	    {
#            print "RULE LEAF: $rule_leafs\nCONFIG LEAF: $config_leafs\n";
            # prepare data structures
            my @rule_ls = split(/&&&&/, $rule_leafs);
            my @rule_ls1 = split(/&&&&/, $rule_leafs);
            my @cfg_ls = split(/&&&&/, $config_leafs);
            
            foreach (@rule_ls)
            {
                # modify each leaf if it contains dots 
                if ($cfg_ls[0] =~ /\.(List|Map|Bag|Set|K|List{K})/ || $cfg_ls[0] =~ /\:(K|List|Map|Bag|Set)/)
                {
                    $cfg_ls[0] = ".$1" if $cfg_ls[0] =~ /\:(K|List|Map|Bag|Set)/;
                    
                    s/^\s+//sg;
                    s/\s+$//sg;
                    
                    if (m/\.\s*\=>/)
                    {
                        s/\Q$&\E/$cfg_ls[0] =>/;
                    }
                    elsif (m/(\=>\s*\.)(?:[^LMBSK])/ || m/(\=>\s*\.$)/)
                    {
                        s/\Q$1\E/=> $cfg_ls[0]/;
                    }
                    elsif ($_ eq ".")
                    {
                        $_ = $cfg_ls[0];
                    }   
                }
                shift(@cfg_ls);
            }
            # use a counter to avoid multiple replacements of the same leaf inside rule
            # this can cause variuos troubles
            my $cnt = 0;
            foreach(@rule_ls1)
            {		
 #               print "RULE: $_\n";
                # if there is a single dot, just replace it with its corresponding type
                if ($_ eq ".")
                {
#                    print "\tRule: $rule1\n";
                    $rule1 =~ s/ \. / $rule_ls[0] /;
#                    print "\trule: $rule1\n";
                }
                else 
                {
                    # count occurences 
                    my $count = () = $rule1 =~ /\Q$_\E/g;
                    # set counter to do the precised number of replacements...only once. :-)
                    $cnt = $count if ($count >= 1 && $cnt == 0);
                    
                    # once for all when counter is set to 1
                    if ($cnt == 1)
                    {
                        $rule1 =~ s/\Q$_\E/$rule_ls[0]/g;
                    }
                    
                    # jump while counter is still bigger than 1
                    if ($cnt > 1)
                    {
                        $cnt = $cnt - 1;
                        # move on in the replacements too
                        shift(@rule_ls);
                        next;
                    }
                    
                }
                shift(@rule_ls);
            }
            
            $rule_leafs = "";
            $config_leafs = "";
	    }
	}
	
	# final replacement
	$ret =~ s/\Q$rule\E/$rule1/gs;
    }
    
    return $ret;
}

# register in $config_leafs and $rule_leafs
# keep order -> corresponding leafs
sub collect_rule_leaf
{
    my $node = (shift);
    
    if (Tree::Nary->is_leaf($node))
    {
	$cfgNode = Tree::Nary->first_child($cfgNode);
	if (defined($cfgNode->{data}))
	{
	    $config_leafs .= $cfgNode->{data} . "&&&&";
	    $rule_leafs .= $node->{data} . "&&&&";
	}
    }
    else 
    {
	$cfgNode = Tree::Nary->find($configSubtree, $Tree::Nary::PRE_ORDER, $Tree::Nary::TRAVERSE_ALL, $node->{data});
    }

#    print "Step: Rule: $rule_leafs\n      Cfg: $config_leafs\n";
    return $Tree::Nary::FALSE;
}

###############################################
#   end replacing dots                        #
###############################################


###############################################
#    modules section                          #
###############################################
my %moduleMap = ();
my %ModuleFileMap = ();
my %FileModuleMap = ();

my $moduleList = "?";
my $fileList = "?";

sub build_module_tree
{
    (my $file, local $_) = (shift, shift);
    
    $fileList .= " $file" if $fileList !~ $file;
    
    my $module = "?";
    my $req = "?";
    my @modules = ();
    my @amodules = ();

    if (/k?mod\s+([^\s]*?)\s+/)
    {
		$module = "$1";
		$module =~ s/\s//g;
		$moduleList .= " $module";
		$ModuleFileMap{$module} = $file;
		my $tempMod = $module;
		$tempMod = $FileModuleMap{$file} . " $tempMod" if defined($FileModuleMap{$file});
		$FileModuleMap{$file} = $tempMod;
	}
    
	my $temp = $_;

    while ($temp =~ m/including([A-Z0-9\s\-\+]+)/sg)
    {
		$req = "$1";
		$req =~ s/^\s*//g;
		$req =~ s/\s*$//g;
		@modules = split(/\s+\+\s+/, $req);
		foreach(@modules)
		{
			push(@amodules, @modules);
		}
    }

	$moduleMap{$module} = @amodules;
	$moduleList .= " @amodules";
   
#	print "MOD: $module\nMAP:@amodules\n\n\n";

    if ($module ne "?")
    {
		$moduleMap{$module} = "@amodules";
    }
        
#    print "\nModule:\n";
#    while( my ($k, $v) = each %moduleMap ) {
#	print "key: $k, value: $v. I: " . includesK($k) . " \n";
#    }
#    print "\nFILE MODULE:\n";
#    while( my ($k, $v) = each %FileModuleMap ) {
#	print "key: $k, value: $v.\n";
#    }
#    print "\nMODULE FILE:\n";
#    while( my ($k, $v) = each %ModuleFileMap ) {
#	print "key: $k, value: $v.\n";
#    }
    
    return $module;
}

# append file to list
sub addFile
{
    my $file = shift;
    $fileList .= " $file" if $fileList !~ $file;    
}

my $subsortations = "";
my $sorts_ = "";# map sorts to modules
my %sortMap = ();
# map modules to sorts
my %sortMod = ();


# register all sorts and subsorts
sub register_subsorts
{
    local $_ = shift;
    my $module = "";
    my $localsorts = "";
    
    # get module name
    if (/k?mod\s+(\S*)\s+/)
    {
	$module = $1;
    }
    
    my $local = $_;

    # register sorts
    while ($local =~ /sort\s+([^<]*?)\s+\./sg)
    {
	$sorts_ .= "$1 ";
	$localsorts .= "$1 ";
	# only for declarations of sorts
	$sortMap{$1} = $module;
    }
    
    # register subsorts and undeclared sorts
    while ($local =~ /subsort\s+(\S+?)\s+<\s+(\S+?)\s+\./sg)
    {
		my $t1 = $1;
		my $t2 = $2;

		$subsortations .= "\n$t1 < $t2";
		$sorts_ .= "$t1 " if $sorts_ !~ /$t1/sg;
		$sorts_ .= "$t2 " if $sorts_ !~ /$t2/sg;
		$localsorts .= "$t1 " if $localsorts !~ /$t1/sg;
		$localsorts .= "$t2 " if $localsorts !~ /$t2/sg;
    }

    # TODO: add all sorts included by included modules
    $localsorts .= " " . getAllModules($module);
    
#	print "ALL: $localsorts\n";

    # add all sorts into %sortMod
    # $localsorts =~ s/\s+$//s;
    $sortMod{$module} = $localsorts;

#    print "Sorts: $sorts_\n";
#    print "\nSORT MODULE:\n";
#    while( my ($k, $v) = each %sortMod ) {
#	print "key: $k, value: $v \n";
#    }

}

my $deep = 0;

sub getAllModules
{
	$deep ++;
    my $mod = shift;
    my $lsorts = "";
    $lsorts = $sortMod{$mod} if (defined($sortMod{$mod}));
    
    my @incl = split(/\s+/, $moduleMap{$mod}) if defined($moduleMap{$mod});
    
    foreach (@incl)
    {
        $lsorts .= " " . getAllModules($_) if $deep < 300;	
    }
    
#	print "DEEP: $deep\n";
    $lsorts;
}

# return true if module includes K
sub includesK
{
    my $module = shift;
	
    return 1 if $module eq "K";
    
    if (!defined($moduleMap{$module})) { return 0; }
    
    my @mlist = split(/\s+/, $moduleMap{$module});
    
    if (scalar(@mlist) > 0)
    {
		foreach(@mlist)
		{
			return 1 if $_ eq "K";
		}
		foreach(@mlist)
		{
		    return 1 if includesK($_);
		}
    }

    return 0;
}

my %supersortmap = ();
# find supersorts list by computing supersorts for each sort
sub find_super_sorts
{
    # remove the empty spaces at the end
    $sorts_ =~ s/\s+$//sg;
        
    # split the list
    my @sorts = split(/\s+/, $sorts_);
    
    # get all supersorts
    foreach(@sorts)
    {
	$supersortmap{$_} = super($_, $subsortations);
    }

    # add all supersorts to the final list only once
    my $supersorts = " ";
    while(my ($k, $v) = each %supersortmap)
    {
#	print "KEY: $k VALUE: $v\n";
	my @values = split(/\s+/, $v);
	my $bool = 0;
	foreach(@values)
	{
#	    print "\tVAL: $k -> $_\n";
	    $supersorts .= "$_ " if ($supersorts !~ /\s($_)\s/);
#	    print "\t\tSSS:|$supersorts|\n";
	    
	    $bool = 1 if ($k_sorts !~ /:$_:/);
	}
	
	$supersorts .= "$k " if ($supersorts !~ /\s($k)\s/) && ($bool == 1);
	
#	print "\n\n";
    }
    
#    print "SUPER: $supersorts\n";
#    print "\nKWD:\n";
#    while( my ($k, $v) = each %supersortmap ) {
#	print "key: $k, value: $v.\n";
#    }
    
    # return the list
    $supersorts =~ s/\s+$//;
    $supersorts
}

sub find_k_sorts
{
    my $ksort = "[A-Z#][A-Za-z0-9\\`\\+\\?\\!#]*(?:\\{[A-Z#][A-Za-z0-9\\`\\+\\?\\!]*\\})?";
    # remove the empty spaces at the end
    my $my_sorts = $sorts_." ";
#    print "SORTS: '$my_sorts' SUBSORTS: $subsortations\n";

    # split the list
    my $subs = $subsortations;
    $subs =~ s/^/ /s if $subs !~ /^\s/s;
    $subs =~ s/$/ /s if $subs !~ /\s$/s;

    while ($subs =~ /\s($ksort)\s+<\s+($non_k_sorts)\s/sg) 
    {
      #print "detected sort $1\n";
        $subs =~ s/\s($ksort)\s+<\s+($non_k_sorts)\s/
        {
        #   print "replacing sort $1\n";
          $non_k_sorts .= "|$1";
          "";
        }/sge;
    }
    $my_sorts =~ s/(?<![0-9a-zA-Z`{}])($non_k_sorts)(?![0-9a-zA-Z`{}])//sg;
    $my_sorts =~ s/\s+$//sg;
#    print "Syntactic Sorts: $my_sorts\n";
    $my_sorts;
}

# given a sort and a set subsortations
# computes recursively all supersorts for the given sort
sub super
{
    # first arg is the sort name
    # second arg is the subsortations set
    (my $sort, my $subs) = @_;
#    print "SORTS: $sort\nSUBS: $subs\n";
     
    return "" if !defined $sort;
    return "" if $subs eq "";
    return "" if $sort eq "";
    
    my @supers = ();
    if (defined($subs))
    {
        $subs =~ s/^/ /s if $subs !~ /^\s/s;
        $subs =~ s/$/ /s if $subs !~ /\s$/s;
        # all supersorts will be stored here
        
#	print "SORT: $sort\nSUBSORTATIONS:\n$subs\n\n\n";
    
        # get all supersorts for the current sort
	if (defined $sort)
	{
	    while ($subs =~ /\s($sort)\s+<\s+(\S+)\s/sg)
	    {
		my $ssubs = $subs;
		$ssubs =~ s/\s($sort)\s+<\s+(\S+)\s/\n/sg;
		push(@supers, super($2, $ssubs));
	    }
	}
    }
    # each sort is its own supersort
    push(@supers, $sort) if scalar(@supers) == 0;
    "@supers";
}

sub find_topmost_module
{
    my @modules = ();
    my $inclusions = "#";
    
    # store the values from module map in some convenient structures
    # each module will be checked -> put it into an array
    # put all "right hand" modules into a variable separated with # for a future match
    while(my ($k, $v) = each %moduleMap) 
    {
        push(@modules, $k);
        my @temp = split(/\s+/, $v);
        foreach(@temp)
        {
            $inclusions .= "$_#";
        }
    }
    
    # collect all modules which are not included by other modules
    my @mods = ();
    foreach (@modules)
    {
	push(@mods, $_) if ($inclusions !~ /#$_#/);
    }   
    
#    print "Modules: @mods\n\n";
    @mods
}


sub getSubsortations
{
    return $subsortations;
}

sub getSorts_
{
    return $sorts_;
}

sub getModuleFile
{
    my $module = shift;
    return $ModuleFileMap{$module};
}


sub exist
{
    my $mod = shift;
    $moduleList .= " ";
    return 1 if ($moduleList =~ / $mod /);
    return 0;
}

sub emptyModuleList
{
    return $moduleList eq "?";
}

sub getModuleList
{
    my $mods = $moduleList;
    $mods =~ s/^[\s\?]+//s;
    my @arr = join(" ", uniq(split(/\s+/, $mods)));    
    return "@arr";
}

sub getFileList
{
    my $list = $fileList;
    $list =~ s/^[\s\?]+//s;
    return $list;
}

sub getFileModules
{
    my $file = shift;
    return $FileModuleMap{$file};
}


sub getModuleSorts
{
    my $mod = shift;
    return $sortMod{$mod} if (defined($sortMod{$mod}));
    return undef;
}

sub uniq 
{
    return keys %{{ map { $_ => 1 } @_ }};
}

###############################################
#   end modules section                       #
###############################################


###############################################
#       line numbers metadata                 #
###############################################

my @k_attributes = qw(binder strict metadata prec format assoc comm id hybrid gather extends ditto parser seqstrict structural anywhere defined transition supercool superheat large latex);
my $k_attributes_pattern = join("|",  @k_attributes);


sub add_metadata
{
        my ($statement, $data) = (shift, shift);
	my $attr = "";
	my $space = "";
	my $bool = 0;
	
	$statement =~ s/(?<=\s)\[([^\[]*?)\](\s*)$/
	{ 
	    $attr = $1; 
	    $space = $2;
	    
#	    print "ATTR: $attr\n";
	    my @ttags = get_tags();
	    foreach(@ttags)
	    {
		if ($attr =~ m!\b\Q$_\E\b!sg)
		{
#		    print "AICI! $attr\n\n";
		    $bool = 1;
		}
	    }
	    ""; 
	}/gse;
        
	
	if ($bool == 0 && $attr ne "")
	{
	    $statement .= "[$attr]$space";
	    $attr = "";
	}
	
#	print "ATT: $attr\n";
	
	if ($attr eq "")
        {
	    $attr = "metadata \"$data\""; 
        }
        else
        {
	    if ($attr =~ /metadata/sg)
	    {
		$attr =~ s/(metadata\s+")/$1$data /sg;
            }
            else
            {
		$attr .= "metadata \"$data\"";
	    }
        }
        $statement .= " ".op_tags($attr).$space;
        return $statement;
}

sub line_numbers
{
    my ($statement, $operation, $spaces, $file) = (shift, shift, shift, shift);

#	print "CHECK: $statement\n";

    if ( $operation eq "rule" or $operation eq "define" or $operation eq "context" or $operation eq "op" or $operation eq "declare")
    {
        my ($rule, $spaces) = ($statement, $spaces);
        my ($tmp, $rule_line, $rule_size) = ($rule, countlines("$`"), countlines("$rule"));
        if ($rule_size > 1) 
        {
          $rule = add_metadata($rule, "location=($file:$rule_line-" . ($rule_size + $rule_line - 1) . ")");
        } else {
          $rule = add_metadata($rule, "location=($file:$rule_line)");
        }
#        $rule =~ s!\[([^\]]*?(?<=(\s|\[))($k_attributes_pattern)(?=(\s|\]))[^\]]*?)\](?=\s*)$!{$attr = $1;}""!gse;
      
#        print "Rule: $rule\n\n\n";
        return $rule . $spaces;
     }
     elsif ($2 eq "macro")
     {
 		# macros
         my $macro = $1;
         my $macro_line = countlines($`);
 #            $temp =~ s/\Q$macro\E/$macro [metadata "location($file:$macro_line)"]/s;
 		return add_metadata($macro, "location=($file:$macro_line)") . $spaces;
     }
	elsif ($2 eq "mb")
	{
	    # mb latex from latex comments
	    my $mb = $1;
	    my $temp_mb = $mb;
	    my $mb_line = countlines($`);
	    
	    $mb =~ s/(mb\s+latex.*)/$1 [metadata "location=($file:$mb_line)"]/sm;
	    # $mb =~ s/(mb\s+latex\s.*?)(\s*)(?=$kmaude_keywords_pattern)/$1 [metadata "location=($file:$mb_line)"]$2/s;
	    
	    return $mb . $spaces;
	}
	elsif ($2 eq "syntax")
	{
		# get the syntax
		my $syntax = $1;
		my $prematch_lines = countlines($`);
		my $original_syntax = $syntax;

		# get productions from syntax block
		if ( $syntax =~ m!syntax\s+(.*)!sg )
		{
			# get all productions
			my $productions_string = $1;
			my $new_prod = "";
	#		print "PROD: $productions_string\n";
	
			my $counter = 1;	
			while ($productions_string =~ /(.*?\S.*?(?:\s\|\s+|$))/gs)
			{
				# process each production
				my $production = $1;
				my $pre = countlines($`);
				my $attributes = "";                                                                                                                        

				# freeze strings before extracting the attributes because these can contain
				# some [] which will cause a wrong extraction
				$production =~ s/($string_pattern)/Freeze($&,"MYS")/sge;
				$production =~ s/(\[[^\[\]]*\]\s*\|?\s*)$/                                                                                    
				{
				    if (op_attribute($1)) {
					$attributes = $1;
					"";
				    } else {$1;}
				}
				/se;
				$production = Unfreeze("MYS", $production); 
				$attributes = Unfreeze("MYS", $attributes); 

				# compute line number
				my $absolute_line = $prematch_lines + $pre - 1;

                                # print "Production1: $production &$attributes&\n";

				# if there are already some attributes then add metadata if other metadata is there
				$attributes =~ s/metadata(\s+)\"(.*?)\"/metadata$1\"$2 location=($file:$absolute_line:$counter)\" / if ($attributes ne "" && $attributes =~ /metadata/);      
				# if there are already some attributes then add metadata if not already                                                                             
				$attributes =~ s/\[/[ metadata \"location=($file:$absolute_line:$counter)\" / if ($attributes ne "" && $attributes !~ /metadata/);
				# if no attributes just define a new attribute metadata and declare location
				$attributes = "[metadata \"location=($file:$absolute_line:$counter)\"]" if $attributes eq "";

				# increase counter
				$counter++;
				
				# unfreeze here what was frozen in $production
				$attributes = Unfreeze("MYS", $attributes);

				#		    print "Production2: $production &$attributes&\n";

				if ($production !~ /(?<!`)\|\s*$/s)
				{
#						print "Production3: $production &$attributes&\n";
				    $production .= " $attributes";
				}
				else 
				{
				    $production =~ s/(\|\s*$)/$attributes $1/s;
				}

				$new_prod = "$new_prod$production";
			   }

			$original_syntax =~ s/\Q$productions_string\E/$new_prod/sg;
		}

		# $temp =~ s/\Q$syntax\E/$original_syntax/s;
		return $original_syntax . $spaces;
	}
	elsif ($2 eq "configuration")
	{
	    my $lines = countlines($`);
	    $statement . " [metadata \"location=($file:$lines)\"]" . $spaces;
	}
 	else { return $statement . $spaces;	}
}

sub add_line_numbers
{
    (local $_, my $file) = (shift, shift);
    
    my $temp;
    s/(?<!\S)((rule|define|syntax|op|declare|macro|context|configuration|mb)\s+.*?)(\s+)(?=$kmaude_keywords_pattern)/
    {
	$temp = line_numbers($1, $2, $3, $file);
    }
    $temp/sge;
    
#    print ;

    $_;
}

sub add_line_no_mb
{
    my  $file = shift;
    my $lines = shift; # get starting line number
    local $_ = shift;
    my $temp = $_;
    
    while($temp =~ /(mb\s+(configuration)\s.*?)(\s\.\s+)(?=($kmaude_keywords_pattern|var|op|mb|eq|ceq|endm))/sg)
    {
#	print "Around\n\n$&\n\n\n";
	my ($content, $end, $line) = ($1, $3, $lines + countlines($`));
	s/\Q$content$end\E/$content [metadata "location=($file:$line)"]$end/sg;
    }
 
     
#    print "$_\n\n";
    return $_;
}

sub countlines
{
    my ($text) = (@_);
    my $lno = ($text =~ tr/\n//);
    
#    return 1 if $lno == 0;
#    return $lno if $text =~ /\n$/;
    return $lno + 1;
}


# Args: K statement
# Return: K statement
# If the K statement is a rule which contains a macro
# then apply that macro ("counter" version)
sub resolve_where_macro($)
{
	local $_ = shift;
	my %macro_map = ();
	my %macro_order = ();
	my $count = 0;
	my $limit = 100;

	# where macro can be found only in rules
	if (/^rule/)
	{
		# locate where macro if any
		if (/(?<=\s)(where(\s+)(.*?))(\s+)(?=ATTR[0-9]*)/sg)
		{ 
			# extract needed data
			my $macros = $3;
			my $all = $&;

			# build an empty string which will keep the 
			# length and the number of lines for where macro
			my $macros_template = $all;
			$macros_template =~ s/[^\n]/ /sg;

			# exclude the where macro from the rule body
			# and replace it with whitespaces
			s/\Q$all\E/$macros_template/sg;

			#			print "MACROS:|$macros|\n";

			# first, collect macros
			# macro_map contains all macros mapped to their values
			# macro_order contains macros occurence order mapped to their names
			while ($macros =~ /(^|and)\s*(\w+)\s+=\s+(.*?)(?=(and|$))/sg)
			{
				#				print "$1\n$2\n$3\n\n";
				$macro_map{$2} = $3;
				$macro_order{$count++} = $2;
			}

			# apply round robin algorithm
			my $round = 0;
			
			# count no of occurences; for debug reasons
#			my $i = 0;			

			# apply the macros until limit is reached
			while ($limit > 0)
			{
				#				print "ROUND: $round COUNT: $count\n\n";
				# round robin; do not change the order of these instructions
				$round ++ if $round < $count;
				$round = 0 if $round == $count;

				# replace macro
				#				s/(?<=[^a-zA-Z])\Q$macro_order{$round}\E(?=[^a-zA-Z0-9])/{print "BEFORE: $_\n"; ++$i; print "R: $round\n";}$macro_map{$macro_order{$round}}/sge;
				s/(?<=[^a-zA-Z])\Q$macro_order{$round}\E(?=[^a-zA-Z])/$macro_map{$macro_order{$round}}/sg if (defined($macro_order{$round}) && defined($macro_map{$macro_order{$round}}));

				# decrement limit
				$limit --;
			}

		#			print "MACRO: $macros\n";
		#			print "ALL: $all\n";
		#			print "RULE: $_\nMACRO REPLACEMENTS:$i\n";
		}
	}
	
	# send back the K statement
	return $_;
}

# the following subroutine replaces 
# macros declared with where
sub resolve_where_macro_old($)
{
    local $_ = shift;
    my %macro_map = ();
    my %macro_order = ();
    my $i = 1;
    
    # where macro can be found only in rules
    if (/^rule/)
    {
        # locate where macro if any
        if (/(?<=\s)(where(\s+)(.*)(\s+))(?=ATTR[0-9]*)/sg)
        { 
            # extract needed data
            my $macros = $3;
            my $all = $&;

            # build an empty string which will keep the 
            # length and the number of lines for where macro
            my $macros_template = $all;
            $macros_template =~ s/[^\n]/ /sg;
            
            
            # exclude the where macro from the rule body
            # and replace it with whitespaces
            s/\Q$all\E/$macros_template/sg;
            
            # first, collect macros
            # macro_map contains all macros mapped to their values
            # macro_order containt all macros mapped to their occurence order
            while($macros =~ /(\w+)\s+=\s+(.*?)((?=(\s+(\w+)\s+=))|$)/sg)
            {
                $macro_map{"$1"} = "$2";
                $macro_order{"$1"} = $i ++;
            }
            
            # solve macros inside macros
            # each macro must be defined before it is used
            # the following code will replace macros in each (key) value
            while(my ($k, $order) = each %macro_order)
            {
                # $order contains the occurence index
                # $k is the curent macro
                # replace macro with its values in all macros declared after it was declared
                while(my ($newk, $mvalue) = each %macro_map)
                {
                    if ($macro_order{$newk} > $order)
                    {
                        # add replacement
                        $mvalue =~ s/\Q$k\E/$macro_map{$k}/sg;
                        $macro_map{$newk} = $mvalue;
                    }
                }
            }
            
            
            # solve macros in current rule
            # each macro in the hashmap $macro_map will be replaced
            # in the current rule with macro's value
            while(my ($k, $v) = each %macro_map)
            {
                s/(?<=\s)\Q$k\E(?=\s)/$v/sge;
            }
        }
    }    
    
    return $_;
}    

# return 1 if the input string is balanced and 0 otherwise
# args: input string, left "brace", right "brace", quoting char
sub balanced($$$$)
{
    # set parameters
    local $_ = shift;
    my ($left, $right, $separator) = (shift, shift, shift);
    
    # exclude any quoted brace
    s/(\Q$separator\E)(\Q$left\E|\Q$right\E)//sg;
    
    # remove balanced
    s/$RE{balanced}{-begin => "$left" }{-end => "$right"}//sg;
      
    # return false if the input string is balanced
    return 0 if (/(\Q$left\E|\Q$right\E)/);
    
    # return true otherwise
    return 1;
}


# Args: receives a module body
# Return: the desugared module body
# Modifies the module body so that
# each <br/> is desugared into @latex("\\kBR")
sub desugar_latex
{	
	# get module 
	my $mod = shift;

	# if there is any configuration
	if ($mod =~ /(?<=\s)configuration\s+.*?\s+(?=$kmaude_keywords_pattern)/sg)
	{
		# keep old config
		my $old_config = $&;

		# keep the new configuration... do the replacement
		my $new_config = $&;

		# replace <br/> with @latex("\\kBR")
		$new_config =~ s/$latex_break/\@latex("\\\\kBR")/sg;

		# replace the old configuration with the new one
		$mod =~ s/\Q$old_config\E/$new_config/sg;
	}

	# keep module to traverse it and modify it in the same time
	local $_ = $mod;

	# foreach rule... do the replacement
	while (/(?<=\s)rule\s+.*?\s+(?=$kmaude_keywords_pattern)/sgm)
	{
		# keep old rule
		my $old_rule = $&;

		# keep the new rule
		my $new_rule = $&;

		# replace <br/> with @latex("\\kBR")
		$new_rule =~ s/$latex_break/\@latex("\\\\kBR")/sg;

		# replace the old rule with the new one
		$mod =~ s/\Q$old_rule\E/$new_rule/sg;
	}

	return $mod;
}



###########################
# comments section - Radu #
###########################

my $special_comment = join("|", (
	"\\/\\/(.*?)\$",
	"\\/\\*(.*?)\\*\\/",
	"---\\((.*?)---\\)",
	"---(.*?)\$",
	"\\*\\*\\*\\((.*?)\\*\\*\\*\\)",
	"\\*\\*\\*(.*?)\$"
));
my %comments_map = ();

sub remove_comments($)
{

	%comments_map = ();
	local $_ = shift;
	
	$_ =~ s/($special_comment)/
	{
		my $line = countlines($`);
		my $comm = "";
		# retrieve the content of the comment from each regexp
		if (defined $2) {
			$comm = $2;
		} elsif (defined $3) {
			$comm = $3;
		} elsif (defined $4) {
			$comm = $4;
		} elsif (defined $5) {
			$comm = $5;
		} elsif (defined $6) {
			$comm = $6;
		} elsif (defined $7) {
			$comm = $7;
		}
		
		my $i = 0;
		# for each line in the comment - put it in the map
		while ($comm =~ m!(.*?)(\n|$)!gsm) {
			if ( $comments_map{$line + $i} ) {
				$comments_map{$line + $i} = "$comments_map{$line + $i} <<~>>$1";
			} else {
				$comments_map{$line + $i} = "$1";
			}
			$i = $i + 1;
		}
		local $_=$1;
		s![^\n]!!gs;
		$_;
	}/gsme;

	return $_;
}


sub put_back_comments($)
{
	my $cod = shift;
	my $fin = "";
	
	my $i = 1;
	while ($cod =~ m/(.*?)(\n|$)/gsm) {
		if ( $comments_map{$i} ) {
			$fin = "$fin$1 ----$comments_map{$i}\n";
		} else {
			$fin = "$fin$1\n";
		}
		$i = $i + 1;
	}
	return $fin;
}

################
# end comments #
################


##################
# latex comments #
##################

# Args: k file content
# Return: k file content
# replace latex comments inside each module
sub solve_latex
{
	local $_ = shift;

	s/(k?mod.*?endk?m)(?!\\end\{)/
	{
	    solve_latex_comments($&);
	}
	/sge;
	
	$_;
}

# Args: k module
# Return: k module
# replaces latex comments inside modules 
# with mb declarations
sub solve_latex_comments
{
    # get k module
    local $_ = shift;
        
    s!($latex_comment)!{
	local $_ = $+;
	my $me = $_;
	$me =~ s/[^\n]//sg;
	"mb latex \"\\\\".get_newcommand($_)."\" : KSentence $me";
    }!sge;
    
    $_;
}

######################
# end latex comments #
######################

# Special: this doesn't stop if there are errors in maude
# Running Maude (cross platform)
sub run_maude_ 
{
	my $input_file = "IN.maude";

	my ($message,@commands) = @_;
	print $message if $verbose;
	open FILE,">",$input_file or die "Cannot create $input_file\n";
	print FILE "\n@commands\n";
	close FILE;

	# call maude
    
#    my $input = File::Spec->rel2abs($input_file);
	my $result = `$maude $input_file 2>&1`;

	# clean
	unlink $input_file;

	# return output
 	return $result;
}

# checks for incompatible sorts
sub check_incompatible
{
	my $file = shift;
	$file =~ s/\.[a-z]+$//sg;

	my $module = shift;	
	
	# get the output from maude and then parse it.
	local $_ = run_maude_("running maude ..",
			"load \"$file\"\n",
			"red in META-LEVEL : sameKind(upModule('$module, true), 'K, 'Map) . \n",
			"red in META-LEVEL : sameKind(upModule('$module, true), 'K, 'List) . \n",
			"red in META-LEVEL : sameKind(upModule('$module, true), 'K, 'Bag) . \n",
			"red in META-LEVEL : sameKind(upModule('$module, true), 'K, 'Set) . \n",
			"red in META-LEVEL : sameKind(upModule('$module, true), 'List, 'Map) . \n",
			"red in META-LEVEL : sameKind(upModule('$module, true), 'List, 'Bag) . \n",
			"red in META-LEVEL : sameKind(upModule('$module, true), 'List, 'Set) . \n",
			"red in META-LEVEL : sameKind(upModule('$module, true), 'Map, 'Bag) . \n",
			"red in META-LEVEL : sameKind(upModule('$module, true), 'Map, 'Set) . \n",
			"red in META-LEVEL : sameKind(upModule('$module, true), 'Bag, 'Set) . \n",
			"q" 
	);

	# silently exit this check if maude returned emply string
	return if !(defined $_);
	
	my $out = $_;
	while ($out =~ /reduce\s+in\s+META-LEVEL\s+:\s+sameKind\(upModule\('$module,\s+true\),\s+'([a-zA-Z]+),\s'([a-zA-Z]+)\)(.*?)result\s+Bool:\s+(true|false)/sg)
	{
		# print "Current:\n$&\n\n";
		local $_ = $&;

		if ($4 eq "true")
		{
			my ($sort1, $sort2) = ($1, $2);

			local $_ = run_maude_("running maude...",
					"load \"$file\"\n",
					"red in META-LEVEL : lesserSorts(upModule('$module, true), '$sort1) . \n",
					"red in META-LEVEL : lesserSorts(upModule('$module, true), '$sort2) . \n",
					"q" );
			# extract results
			my ($list1, $list2) = ("", "");
			s/result\s+[a-zA-Z]+:(.*?)(?=\n)/{$list1 = $1;}/se;
			s/result\s+[a-zA-Z]+:(.*?)(?=\n)/{$list2 = $1;}/se;

#			print "Error: $sort1 and $sort2 have the same kind.\nThis error may occur when $sort1 and $sort2 have common lesser sorts.\nLesser sorts for $sort1: $list1\nLesser sorts for $sort2: $list2\n\n";
			print wrap("", "", generate_error("ERROR", 1, $file, "unknown line", "$sort1 and $sort2 have the same kind.\nThis error may occur when $sort1 and $sort2 have common lesser sorts.\nLesser sorts for $sort1: $list1\nLesser sorts for $sort2: $list2"));
			exit(1);
		}
	}
}



# Args: file, and the relative path of imported file
# Return: file path
# search the apropriate import
sub maudify
{
    my $import = shift;
    my $file = shift;
    
    my $m_import = $import;
    $m_import =~ s!^\/!!sg;
    
#		print "\n\nIMP: $import\nFILE: $file\n\n";
    
    # solve local files
    if (-e File::Spec->catfile((fileparse($file))[1], $import))
    {
	# $import is a local file, $import contains extension
	return File::Spec->catfile((fileparse($file))[1], $import);
    }
    elsif (-e File::Spec->catfile((fileparse($file))[1], "$import.k"))
    {
	# $import is a local file, $import is a k file
	return File::Spec->catfile((fileparse($file))[1], "$import.k");
    }
    elsif (-e File::Spec->catfile((fileparse($file))[1], "$import.maude"))
    {
	# $import is a local file, $import is a maude file
	return File::Spec->catfile((fileparse($file))[1], "$import.maude");
    }
    
    # solve absolute paths
    elsif (-e $import)
    {
	# $import contains extension
	return $import;
    }
    elsif (-e "$import.k")
    {
	# $import is a k file
	return "$import.k";
    }
    elsif (-e "$import.maude")
    {
	# $import is a local file, $import is a maude file
	return "$import.maude";
    }
    
    # solve imports from K_BASE modules
    elsif (-e File::Spec->catfile($k_base, $m_import))
    {
	# $import contains extension
	return File::Spec->catfile($k_base, $m_import);	
    }
    elsif (-e File::Spec->catfile($k_base, "$m_import.k"))
    {
	# $import is a k file
	return File::Spec->catfile($k_base, "$m_import.k");
    }
    elsif (-e File::Spec->catfile($k_base, "$m_import.maude"))
    {
	# $import is a maude file
	return File::Spec->catfile($k_base, "$m_import.maude");
    }
    
    print wrap("", "", generate_error("ERROR", 1, $file, "unknown line", "File $import needed by $file cannot be found! Please check if the path is correct."));
}

sub process_tags
{
    my $arg = shift;
    my @args = ();
    
    while ($arg =~ /\s*([^(?<!`)\(\s]+)\s*((?<!`)\(.*?(?<!`)\))?/sg)
    {
	last if $1 =~ /^-/sg;
	push(@args, "$1=$2") if defined $2;
	push(@args, "$1=()") if ! defined $2;
    }
    
    "@args";
}

    
    
sub get_checksum 
{
    my $md5 = Digest::MD5->new;
    
    foreach my $file (@checksum_files) 
    {
	open(F, $file);
	$md5->addfile(*F);
	close(F);
    }
    return $md5->hexdigest;
}

#########################
# TAGS                  #
#########################

# predefined tags
my @tags = split(",", "metadata,location,ditto,prec,parser,latex,hybrid,arity,extends,seqstrict,strict,binder,wrapping,structural,anywhere,defined,transition,supercool,superheat,computational,large,tag,strat,frozen");


sub get_tags
{
    return @tags;
}

# tags : nondet etc mytag
# parse all tags and put them in @tags
sub parse_tags
{
    local $_ = shift;
    s/([^(?<!`)\(\s]+(\s*(?<!`)\(.*?(?<!`)\))?)/
    {
	push(@tags, $1);
	"";
    }
    /sge;
}


sub rule_tags
{
    my $all = shift;
    $_ = $all;
    
    while ( $all =~ /rule(.*?\s)(?=$kmaude_keywords_pattern)/sg )
    {
	
	my $body = $1;
	
	# get rule name 
	my $rule_name = "";
	$rule_name = $1 if $body =~ /^\s*\[\s*(\S+)\s*\]\s*:/sg;
	
	# get attributes
	my $attributes = "";
	my $spaces = "";
	if ($body =~ /(?<=\s)(\[[^\[]*?\])(\s*)$/sg)
	{
	    my $attributes = $1;
	    
#	    print "ATTR: $attributes\n\n";
	    
	    my $spaces = $2;
	    my $temp_attributes = $attributes;
	  
	    my @tagss = ();
	    
	    # keep metadata into another variable
	    my $metadata = "";
	    $attributes =~ s/metadata\s+"(.*?(?<!\\))"/
	    {
		$metadata = $1;
		"";
	    }/sge;
	    
#	    print "Body: $body\nATTR: $attributes\n";
	    # first: collect tag:mytag declarations in @tags
	    $attributes =~ s/\btag\s*:\s*([^(?<!`)\(\s\]]+((?<!`)\(.*?(?<!`)\))?)/
	    {
		push(@tags, $1);
		push(@tagss, $1);
		"";
	    }
	    /sge;
	    
	    # remove all declared tags from attributes
	    # those attributes which are not removed are not declared..
	    # collect them in @tagss
	    foreach(@tags)
	    {
		push(@tagss, $_) if $attributes =~ /\b\Q$_\E\b/sg;
		$attributes =~ s/\b\Q$_\E\b//sg;
	    }
	    
	    # clean [, ] and \s* => $attributes should be clean ...
	    $attributes =~ s/^\s*\[//s;
	    $attributes =~ s/\]\s*$//s;
	    # $attributes =~ s/\s+//sg; 

	    if ($attributes =~ /\S/sg)
	    {
#		print "[ERROR] at $metadata: You have some undeclared tags: \"$attributes\"\n";
#		exit(1);
	    }
	   
	    # re-build the attributes
     	    $attributes = "";
	    
	    # complete metadata
	    foreach(@tagss)
	    {
		s/(?<!`)\(/=(/s if /(?<!`)\(/sg;
		$_ .= "=()" if $_ !~ /(?<!`)\(/sg;
		$metadata .= " $_"
	    }

	    my $keep = "";
	    $keep = "label $rule_name" if $rule_name ne "";
	    $metadata .= " $rule_name=()" if $rule_name ne "";
		
	    $attributes  = "metadata \"$metadata\" $keep";

#	    print "AFTER: $attributes\n";
		
	    # update body
	    my $temp_body = $body;
	    $body =~ s/\Q$temp_attributes\E/[$attributes]/s;

	    $body =~ s/^\s*\[\s*(\S+)\s*\]\s*://sg;
		
	    # update rule
	    s/\Qrule$temp_body\E/rule$body/s;
	       
	}
    }
    
    $_;
}
    
sub oper_tags
{
    local $_ = shift;
    
    my $temp = $_;
    
#    while($temp =~ /op(.*?)\[.*?\]\

    $_;
}
    
sub op_tags
{
    local $_ = shift;
    
    my $attributes = $_;
    my @tagss = ();
    
    my $spaces = $1 if $attributes =~ /(\s*$)/sg;
    
#    print "ATTR: $attributes\n";
    
    # keep metadata into another variable
    my $metadata = "";
    $attributes =~ s/metadata\s+"(.*?(?<!\\))"/
    {
	$metadata = $1;
	"";
    }/sge;
	    
    my $keep = "";
    
    # prec
    $attributes =~ s/\b(prec\s*\(?\s*[0-9]+\s*\)?)/
    {
	my $prec = $1;
	$prec =~ s!\(! !sg;
	$prec =~ s!\)!!sg;
	$keep .= " $prec";
	"";
    }
    /sge;

    # strict
    $attributes =~ s/\b((seq)?strict\s*\(.*?\))/
    {
	my $strict_p = $1;
	$strict_p =~ s!\(!=(!s;
	$metadata .= " $strict_p";
	"";
    }
    /sge;
    
    # strat
    $attributes =~ s/\b(strat\s*\(.*?\))/
    {
	$keep .= " $1";
	"";
    }
    /sge;

    # frozen
    $attributes =~ s/\b(frozen\s*\(.*?\))/
    {
	$keep .= " $1";
	"";
    }
    /sge;

    # gather
    $attributes =~ s/\b(gather\s*\(.*?\))/
    {
	$keep .= " $1";
	"";
    }
    /sge;

    # latex
    $attributes =~ s/\b(latex\s*\(?".*?"\)?)/
    {
	local $_ = " $1";
	s!latex\s*\("(.*?)"\)!{ "latex=(renameTo \\\\" . get_newcommand($1) . ")"; }!se;
	s!latex\s*"(.*?)"!{ "latex=(renameTo \\\\" . get_newcommand($1) . ")"; }!se;
	$metadata .= " $_";
	"";
    }
    /sge;
    
    # ditto
    $attributes =~ s/\b(ditto)\b/
    {
	$keep .= " $1";
	$metadata .= " $1=()";
	"";
    }
    /sge;

    # id:
    $attributes =~ s/\b(id\s*:\s+[^\s\]]+)/
    {
	$keep .= " $1";
	"";
    }
    /sge;

    # id()
    $attributes =~ s/\b(id\s*\([^\s\]]+\))/
    {
	my $id = $1;
	$id =~ s!id\s*\((.*?)\)!id: $1!sg;
	$keep .= " $id";
	"";
    }
    /sge;

    # assoc
    $attributes =~ s/\b(assoc)\b/
    {
	$keep .= " $1";
	"";
    }
    /sge;

    # comm
    $attributes =~ s/\b(comm)\b/
    {
	$keep .= " $1";
	"";
    }
    /sge;

    # format
    $attributes =~ s/\b(format\s*\(.*?\))/
    {
	$keep .= " $1";
	"";
    }
    /sge;
    
    
#    print "1-ATTR: $attributes\n";
    # first: collect tag:mytag declarations in @tags
    # $attributes =~ s/\btag\s*:\s*([^(?<!`)\(\s\]]+((?<!`)\(.*?(?<!`)\))?)/
    $attributes =~ s/\b\s*([^(?<!`)\(\s\]]+((?<!`)\(.*?(?<!`)\))?)/
    {
	my $tg = $1;
	$tg =~ s!\(\"!(!sg;
	$tg =~ s!\"\)!)!sg;
	push(@tags, $tg);
	push(@tagss, $tg);
	"";
    }
    /sge;
    
    # remove all declared tags from attributes
    # those attributes which are not removed are not declared..
    # collect them in @tagss
    foreach(@tags)
    {
	push(@tagss, $_) if $attributes =~ /\b\Q$_\E\b/sg;
	$attributes =~ s/\b\Q$_\E\b//sg;
    }

    
    
    # clean [, ] and \s* => $attributes should be clean ...
    $attributes =~ s/^\s*\[//s;
    $attributes =~ s/\]\s*$//s;
    # $attributes =~ s/\s+//sg; 
    
    if ($attributes =~ /\S/sg)
    {
	print wrap("", "", "[ERROR] at $metadata: Undeclared tag(s): \"$attributes\"\n");
	exit(1);
    }
    
    # re-build the attributes
    $attributes = "";
    
    # complete metadata
    foreach(@tagss)
    {
	s/(?<!`)\(/=(/s if /(?<!`)\(/sg;
	$_ .= "=()" if $_ !~ /(?<!`)\(/sg;
        $metadata .= " $_"
    }
	
    $attributes  = "$keep metadata \"$metadata\"";
	   
 #   print "LAST: $attributes\n\n";
	
    "[$attributes]$spaces";
}


	
	
#####################
# Slurp all files   #
#####################

# Globals
my @loaded_files = ();
	
	
# ARGS: main language file, $latex if enabled
# RETURN: the slurped file
# Recurse int all k files and create one k file
sub slurp_k
{
    # retrieve main file
    my $file = shift;
    my $latex_ = shift;
    
    # convert file path to absolute path
    $file = File::Spec::Link->full_resolve(File::Spec->rel2abs($file));
    
    # get file content
    local $_ = get_file_content($file);
    
    # UGLY but useful: remove : from [: :]
    s/\[\:/[/sg;
    s/\:\]/\]/sg;
    
    # md5 
    my $digest = md5_hex($_);
    return "\n" if file_loaded($digest);
    
    # global pre-processing
    $_ = pre_process($_, $latex_, $file);
    
#	print;
    # get file directory
    my $file_dir = dirname($file);
    
    # Freeze modules
    s/(kmod.*?endkm)/Freeze($&, "KMOD")/sge;
    
    # recurse
    s/^\s*(in|load|require)\s+(\S+?)\s*(?=\n)/
    {
	my $import = $2;

	if (!File::Spec->file_name_is_absolute($import))
	{
	    $import =~ s!^\.\/!!s;
	    $import =~ s!^\/!!s;
	}
	
	# case 1: import modules relative to $file
#	print "BEFORE: $file_dir, $import\n";
	my $path;
	if (File::Spec->file_name_is_absolute($import))
	{
#	    print "AROUND!\n";
	    $path = $import;
	}
	else
	{
	    $path = get_full_name_custom(File::Spec->catfile($file_dir, $import));
	}
#	print "PATH: $path\n";
	if (-e $path)
	{
	    slurp_k($path, $latex_);
	}
	else
	{
	    # case 2: import modules relative to $K_BASE
	    $path = get_full_name_custom(File::Spec->catfile($ENV{'K_BASE'}, $import));

	    if (-e $path)
	    {
		slurp_k($path, $latex_);
	    }
	    else
	    {
		print wrap("", "", "[ERROR] Cannot import file $import in $file\n");
		exit(1);
	    }
	}
    }
    /sgme;

    # Unfreeze modules
    $_ = Unfreeze("KMOD", $_);
    
    # put a header
#    $_ = header($file) . $_;
    
    # return
    $_;
}
	

	
# ARGS: file name
# Return: a string like:
#	*************
#       *** $file ***
#       *************
sub header
{
    my $file = shift;
    my $surrounding = "****$file****";
    $surrounding =~ s/./*/sg;
    "$surrounding\n*** $file ***\n$surrounding\n\n\n";
}
	
my @modules = ();
    
sub get_all_modules
{
    \@modules;
}
    
# ARGS: file content, $latex if enabled
# RETURN: file content
# Pre-process the main file:
# - remove comments
# - solve latex comments
# - replace module with kmod and end module with endkm
# - parse configuration
# - add line numbers metadata
sub pre_process
{
    local $_ = shift;
    my $latex_ = shift;
    my $file = shift;
    my $random = 0;
    
    # Step: replace module with kmod and
          # freeze strings
          s/($string_pattern)/Freeze($&,"YSTRINGS")/sge;

          # freeze comments
          s/($comment)/Freeze($&, "CMTS")/sge;

    # Step: remove tags
    s!tags(\s.*?\S)(\s*)(?=$kmaude_keywords_pattern|CMTS)!{parse_tags($1);"$2";}!sge;
    
    
        # endmodule with endkm
        s/\b(module)\b(.*?)(end\s+?module)\b/kmod$2endkm/sg;
    
        # replace including with imports
        s/(?<!\S)imports(?!\S)/including/sg;
    
        # append "is" if necessary
        s/(kmod\s+\S+)(\s+)(?!is)/$1 is$2/sg;

          # unfreeze comments
          $_ = Unfreeze("CMTS", $_);
          # unfreeze comments
          $_ = Unfreeze("YSTRINGS", $_);

    
        # Freeze modules
    s/(kmod.*?endkm)/Freeze($&, "KMOD")/sge;
    
    s/\/\*!(.*?)\*\//
    {
	$preamble = $1;
	""
    }/sme;

    s/(\/\/@.*?$)/
    {
#	print "Comment: $1\n";
	$random++;
	Freeze(" kmod COMMENT-LATEX-GENERATED$random is   $1   endkm", "KMOD");
    }/sme;
    
#    print ;
    
    s/(\/\*\@.*?\*\/)/
    {
#	print "Comment: $1\n";
	$random++;
	Freeze(" kmod COMMENT-LATEX-GENERATED$random is   $1   endkm", "KMOD");
    }/sge;
    
# print;

    $_ = Unfreeze("KMOD", $_);
    # exit;

    # collect all modules
    while(/kmod\s+([A-Z0-9\-]+)\s+.*?endkm/sg)
    {
	push(@modules, $1) if ($1 ne "URIS" && $1 ne "K-VISITOR" && $1 ne "SUBSTITUTION");
    }
    
    # Step: resolve latex comments
    $_ = solve_latex($_) if $latex_;

          # freeze strings
          s/($string_pattern)/Freeze($&,"YSTRINGS")/sge;

    # save comments
    my ($noComments, $myComments) = remove_comments($_);
    $_ = $noComments;
    
          # unfreeze comments
          $_ = Unfreeze("YSTRINGS", $_);

    # add line numbers metadata
    $_ = add_line_numbers($_, $file);

    # return
    $_;
}
	
# ARGS: md5 of a file
# RETURN: true if file already loaded
# Return true if file already loaded and 
# false if not; also append file in @loaded_files
sub file_loaded
{
    my $md = shift;
    
    # return 1 if file already loaded
    for(@loaded_files)
    {
	return 1 if ($md eq $_);
    }
    
    # return 0 and append file in @loaded_files if not loaded
    push(@loaded_files, "$md");
    
    0;
}
	

	
	
	
	
############################
# Freezing                 #
############################	
	
# a map with frozen strings
my %freeze_map = ();
	
	
# a new version of freezing: use digest - md5
sub Freeze
{
    my ($string, $marker) = (shift, shift);
    my $md5_custom = md5_hex($string);
    $md5_custom =~ s/([a-z])/int(rand(9))/sge;
    my $frozen_string = $marker . $md5_custom; # join("", map(ord, split('',md5($string))));
    $freeze_map{$marker}{$frozen_string} = $string;
    
    return $frozen_string;
}
	
# unfreezing (newest version) : use digest - md5
sub Unfreeze
{
    my ($marker, $all) = (shift, shift);
    my $marker_map = $freeze_map{$marker};
    if (defined $marker_map)
    {
	my %map = %$marker_map;
	
	$all =~ s/($marker([a-f0-9]{32}))/defined $map{$1}?$map{$1}:$1/gse;
    }
    return $all;
}
	
	
######################
# syntax with quotes #
######################

sub remove_quotes
{
    local $_ = shift;

    # freeze latex
    s/latex\(\".*?\"\)/Freeze($&, "LTXATTR")/gse;
    
    
    # freeze attributes
    s/(\[\s*metadata.*?\])/Freeze($&, "QUOTES")/gse;
    
    
    # freeze lists
    s/List\{.*?\}/Freeze($&, "QUOTES")/gse;
    
    s/\bsyntax\b.*?(?=$kmaude_keywords_pattern)/
    {
	my $tmp = $&;
	my $tmp1 = $tmp;
	
	my $quotes_number = 0;
	$quotes_number ++ while $tmp =~ m%(?<!\\)\"%sg;
	$quotes_number ++ while $tmp =~ m%(?<=\\\\)\"%sg;
	
#	print "QUOTES:$quotes_number\n";
	
	if ($quotes_number % 2 == 1)
	{
	    $tmp1 = Unfreeze("QUOTES", $tmp1);
	    $tmp1 =~ s!(\[[^\]]*?(metadata)[^\]]*?\])!!gs;
	    print wrap("", "", "[Warning] This warning is thrown when quotes around terminals are not balanced. Notice that if you want to use quotes in your syntax use backslash (\) to escape them. It seems that you forgot a quote (\") in syntax declaration:\n$tmp1\n");
	}

	$tmp =~ s%(?<!\\)\"%KSYNQUOT%sg;
	# Special case for \\"
	$tmp =~ s%(?<=\\\\)\"%KSYNQUOT%sg;

	$tmp =~ s%KSYNQUOT(.*?)KSYNQUOT% `$1 %sg;
	$tmp =~ s%\\(?=\")%%sg;
	$tmp =~s!\\\\!\\!sg;
	$tmp;
    }/gse;

    $_ = Unfreeze("QUOTES", $_);
    $_ = Unfreeze("LTXATTR", $_);

    $_;
}

    
#######################################################
#   Parsing Maude error messages                      #
#######################################################
    

sub parse_maude_error
{
    local $_ = shift;
    my $error_file = shift;
    my $maude_file = shift;

    if (!(-e $maude_file))
    {
	$maude_file .= ".maude";
    }
    
    my $err = "Check .k/$error_file to find all errors.\n";
    
    # replace Warning: Error: and <automatic>:
    s/Warning:(\s*)/Error:$1/sg;
    s/<automatic>:\s*//sg;
    
    my $max_lines = 7;
    my $msg = "";
    while (/.*?(?=\n)/gs)
    {
	if (length $& > 77)
	{
	    $msg .= substr($&, 0, 77) . "...\n";
	}
	else
	{
	    $msg .= $&;    
	}
	
	last if ($max_lines --)== 0;
    }
    
    my $msg1 = "Maude rejected the file .k/$maude_file generated by kompile. Below is a summary of the maude error. Line numbers refer to the generated Maude file at .k/$maude_file but the \"location\" metadata attributes in the generated Maude file refer to the original K definition:";
    my $msg2 = "These usually indicate similar problems in your K definition.\n";
    
    if (length $err > 0)
    {
	return $msg1 . "\n" . $msg . "...\n" . $err . $msg2;
    }
    else {
	return $msg1 . "\n" . $msg . "\n" . $msg2;
    }
}

#################
### functions ###
#################
my $declarekwd = "declare";
my $definekwd = "define";

sub process_functions
{
	my $var = shift;

	# Handle define and declare separately because
	# they need different sort processing.
	# And, of course, people often change their mind...
	
	# declarations (declare) are changed into ops
	$var =~ s/(?<=\n)(\s*)($declarekwd\b.*?)(?=\n\s*($declarekwd|$definekwd|$kmaude_keywords_pattern))/
	{
		my $declaration = $2;
		my $spaces = $1;
#		print "M1: $declaration\n";
		$declaration =~ s!^($declarekwd)!op!s;
#		$declaration =~ s!$ksort!K!sg;
		$declaration = add_metadata($declaration, "function=()");
		"$spaces$declaration";
	}/sge;

	# definitions (define) are changed into rules
	$var =~ s/(?<=\n)(\s*)($definekwd\b.*?)(?=\n\s*($declarekwd|$definekwd|$kmaude_keywords_pattern))/
	{
		my $declaration = $2;
		my $spaces = $1;
		$declaration =~ s!^($definekwd)!rule!s;
		$declaration = add_metadata($declaration, "function=()");
#		print "M2: $declaration\n";
		"$spaces$declaration";
	}/sge;
	
	$var;
}

1;
