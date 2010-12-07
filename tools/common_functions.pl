# !usr/bin/perl -w
use strict;
use warnings;
use File::Spec;
use File::Basename;
use File::Temp qw / tempfile /;

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
my $warnings_file = fresh("kompile_warnings", ".txt");
my $comment = join("|", (
    "---\\(.*?---\\)",                                                                                                            
    "---.*?\$",                                                                                                                   
    "\\*\\*\\*\\(.*?\\*\\*\\*\\)",                                                                                                
    "\\*\\*\\*.*?\$"                                                                                                              
));     
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

my @kmaude_keywords = qw(context rule macro eq configuration op ops syntax kvar sort sorts subsort subsorts including kmod endkm);
my $kmaude_keywords_pattern = join("|",map("\\b$_\\b",@kmaude_keywords));

my $parentheses = "\Q{}[]()\E";
my $maude_backquoted = "(?:`\\(|`\\)|`\\{|`\\}|`\\[|`\\]|`\\,|_|[^$parentheses\\s\\,\\`])*";

# Pattern matched by K variables
my $klabel_body = "$maude_backquoted\_$maude_backquoted";
my $klabel = "'$klabel_body(?:[$parentheses\\s\\,])|$klabel_body(?=\\()";
my $kvar  = "[A-Za-z][A-Za-z0-9]*";


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
    if (-e $warnings_file)
    {
	local $/=undef; open FILE,"<", $warnings_file or print ""; local $_ = <FILE>; close FILE;
    
	if (/error(.*?)\n/isg)
	{
	    "Error $1";
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

# unquote maude metadata in order to speedup the tool
sub unquote 
{
    my ($input) = @_;
    my @values = split('\n', $input);
    my $result = "";
    foreach my $line (@values) 
    {
	chomp($line);
	# first adjust whitespace and colors
	$line =~ s/'\\n /\n/g;
	$line =~ s/'\\t /\t/g;
	$line =~ s/'\\r /\r/g;
	$line =~ s/'\\[ogb] //g;
	$line =~ s/'\\s / /g;

	$line =~ s/metadata\((".*?")\)/metadata $1/; # removes parens from metadata
	$line =~ s/label\((.*?)\)/label $1/; # removes parens from label
	$line =~ s/prec\((\d*)\)/prec $1/; # removes parens from prec
	$line =~ s/^\s*none//; # removes none sections
	$line =~ s/nil -> /-> /; # removes nil op arguments
	my $operatorClass = '(?:(?:`[\(\)\[\]\{\},])|[^\(\)\[\]\{\}, ])';
	my $sortClass = '(?:(?:`[\{\}])|[^_\(\)\[\]\{\},\. `])';
	my $containerClass = '(?:List`\{K`\}|Set|Bag|Map|K|List)';
	my $sortTerminator = '(?:[ ,\]\)])';

	$line =~ s/'($operatorClass+)\.($containerClass)($sortTerminator)/\('$1\)\.$2$3/g; # quoted constants
	$line =~ s/'($operatorClass+)\.($sortClass+)($sortTerminator)/\('$1\)\.$2$3/g; # quoted constants
	$line =~ s/'"(([^"]|([\\]["]))*?)"\.([^ ,\]])/\("$1"\)\.$4/g; # string constants
	$line =~ s/([^ `])\[/$1\(/g; # changes [ into (
	$line =~ s/\] \./FSLENDLQQQ/; # saves attribute brackets
	while ($line =~ s/([^`])\]/$1\)/g){ } # changes ] into )
	while ($line =~ s/sorts ([^ ]*?) ;/sort $1 . sorts/g){ } # separates out sorts
	$line =~ s/FSLENDLQQQ/\] \./; # replaces attribute brackets
	$line =~ s/\[none\]//g; # remove [none] attributes
	$line =~ s/'([^ \)\(,\[\]\{\}]+)/$1/g; # removes all other quotes
        $result .= "$line\n";
    }
   
    return $result;
}


sub getFullName
{
    my $file = (shift);
    if ($file eq "")
    {
	return $file;
    }

    #  hardcoded to avoid maudification for shared.maude
    if ($file =~ /shared\.maude$/)
    {
	return $file;
    }
    
    $file =~ s/^\.\///;

    # If $file has extension .k, .kmaude or .maude then tests if $file exists and errors if not
    
    if ($file =~ /\.k?(maude)?$/) {
	if (! -e $file) {
	    print("File $file does not exist\n");
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
	# Otherwise error: we only allow files with extensions .k, .kmaude or .maude
	else {
	    print("Neither of $file.k, $file.kmaude, or $file.maude exist\n");
	    exit(1);
	}
    }
    return $file;
}

sub appendFileInTree
{
    my ($child, $parent) = (shift, shift);
        
    $child = getFullName($child);
    $parent = getFullName($parent);

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
    my $file = getFullName(shift);
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
    
    while (s/^(\s*)($top_level_pattern)(\s*)//sm) 
    {
	(my $before, local $_, my $after) = ($1,$2,$3);
        if (m!^kmod\s+(\S+)!) {
	    $declaredKLabels .= " " . getDeclaredKLabelList($_);
#	    print "Declared: $declaredKLabels\n";
	}
	elsif (m!^(?:in|load|require)\s+(\S+)!) {
	    my $in = File::Spec->catfile((fileparse($file))[1], $1);
	    my $v_node = Tree::Nary->find($inclusionFileTree, $Tree::Nary::PRE_ORDER, 
	    $Tree::Nary::TRAVERSE_ALL, getFullName($in));
#	    print "\nFile $in \n\n";
	    if (!$v_node)
	    {
#		print "IF $in\n";
		appendFileInTree($in,$file);
		recurseIntoFiles($in);
	    }
#	    printTree();
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
  return "$labels : -> KLabel [metadata \"generated label\"] . ";
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
	my $file = getFullName($current_node->{data});
	my $out = "";
	
	if ($file =~ /\.k(maude)?$/)
	{
		#~ go to leaves first
		Tree::Nary->children_foreach($current_node, $Tree::Nary::TRAVERSE_ALL, \&recurseFlat);
	}
	else {return;}

	local $/=undef; open FILE,"<",$file or die "Cannot open $file\n"; local $_ = <FILE>; close FILE;

	$out = "\n--------- File: $file -----------------\n\n";
	while (s/^(\s*)($top_level_pattern)(\s*)//sm) 
	{
		(my $before, local $_, my $after) = ($1,$2,$3);
		if (m!^(?:in|load)\s+(\S+)!) 
		{
			#~ do nothing;
			my $line = $_;
			my $decl = getFullName($1);
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

# determine whether a file can include other files
sub required()
{
#    printTree();
    my ($p, $c) = (shift, shift);
#    print "P: $p C: $c\n";

    $p =~ s/^\.\///;
    
    $p = Tree::Nary->find($inclusionFileTree, $Tree::Nary::PRE_ORDER, 
	$Tree::Nary::TRAVERSE_ALL, getFullName($p));
    
    while ($p->{data} =~ m/(\.\.\/)/g)
    {
	$c = $1 . $c;
    }
    
#    my $c = File::Spec->catfile((fileparse($file))[1], $c);
#    print "Child: $c\n";
    my $n = Tree::Nary->find_child($p, $Tree::Nary::TRAVERSE_ALL, getFullName($c));
#    print "\n NODE: " . $n->{data} . "\n\n";
    
    if (!$n)
    {
	return 0;
    }
#    print "Found! " . $p->{data} . " parent for " . getFullName($c) . "\n\n\n";
    return 1;
}


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

sub replace_dots
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
		# get corresponding subtree from configuration tree
		$tmp_cfg = Tree::Nary->find($configuration_tree, $Tree::Nary::PRE_ORDER, $Tree::Nary::TRAVERSE_ALL, $temp_rule->{data});
		$configSubtree = $tmp_cfg;
		
		# assign to each leaf inside rule tree its corresponding leaf from configuration tree
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
		    # if there is a single dot, just replace it with its corresponding type
		    if ($_ eq ".")
		    {
			$rule1 =~ s/ \. / $rule_ls[0] /;
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
    
    if (/is\s+including([A-Z\s\-\+]+)/)
    {
	$req = "$1";
	$req =~ s/^\s*//g;
	$req =~ s/\s*$//g;
	@modules = split(/\s+\+\s+/, $req);
	$moduleMap{$module} = @modules;
	$moduleList .= " @modules";
    }
    
    if ($module ne "?")
    {
	$moduleMap{$module} = "@modules";
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
    
    # register sorts
    while (/sort\s+([^<]*?)\s+\./sg)
    {
	$sorts_ .= "$1 ";
	$localsorts .= "$1 ";
	# only for declarations of sorts
	$sortMap{$1} = $module;
    }
    
    # register subsorts and undeclared sorts
    while (/subsort\s+(\S+?)\s+<\s+(\S+?)\s+\./sg)
    {
	my $t1 = $1;
	my $t2 = $2;

	$subsortations .= "$t1 < $t2\n";
	$sorts_ .= "$t1 " if $sorts_ !~ /$t1/sg;
	$sorts_ .= "$t2 " if $sorts_ !~ /$t2/sg;
	$localsorts .= "$t1 " if $localsorts !~ /$t1/sg;
	$localsorts .= "$t2 " if $localsorts !~ /$t2/sg;
    }

    # TODO: add all sorts included by included modules
    $localsorts .= " " . getAllModules($module);
    
    # add all sorts into %sortMod
    # $localsorts =~ s/\s+$//s;
    $sortMod{$module} = $localsorts;

#    print "Sorts: $sorts_\n";
#    print "\nSORT MODULE:\n";
#    while( my ($k, $v) = each %sortMod ) {
#	print "key: $k, value: $v \n";
#    }

}

sub getAllModules
{
    my $mod = shift;
    my $lsorts = "";
    $lsorts = $sortMod{$mod} if (defined($sortMod{$mod}));
    
    my @incl = split(/\s+/, $moduleMap{$mod}) if defined($moduleMap{$mod});
    
    foreach (@incl)
    {
        $lsorts .= " " . getAllModules($_);	
    }
    
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
    my $supersorts = "";
    while(my ($k, $v) = each %supersortmap)
    {
	my @values = split(/\s+/, $v);
	foreach(@values)
	{
	    $supersorts .= "$_ " if ($supersorts !~ /($_)/);
	}
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

# given a sort and a set subsortations
# computes recursively all supersorts for the given sort
sub super
{
    # first arg is the sort name
    # second arg is the subsortations set
    (my $sort, my $subs) = @_;
    
    # all supersorts will be stored here
    my @supers = ();

    # get all supersorts for the current sort
    while ($subs =~ /($sort)\s+<\s+(\S+)/sg)
    {
	push(@supers, super($2, $subsortations));
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


1;
