#!/usr/bin/env perl


use strict;
use warnings;
use POSIX;

my $ksort = "[A-Z#][A-Za-z0-9\\`\\+\\?\\!#]*(?:\\{[A-Z#][A-Za-z0-9\\`\\+\\?\\!]*\\})?";
my @kmaude_keywords = qw(context rule macro eq ceq configuration op ops syntax kvar sort sorts subsort subsorts including kmod endkm mb tags);
my $kmaude_keywords_pattern = join("|",map("\\b$_\\b",@kmaude_keywords));


my $nelist = "Syntactic";
my $elist  = "Semantic";
my $list   = "";

my $counter = 7;

my %declaration_map = ();
my %constructors = ();
my %declared_list = ();
my %list_attributes_map = ();

sub solve_lists
{
    local $_ = shift;
    my $temp = $_;
    
    # store generated code
    my $generated_code = "";
    
    # presupunem: | syntax Ids ::= List{#Id, ","} [attributes] |
    # iterate through syntax declarations
    while ($temp =~ /(syntax\s+($ksort)\s*::=\s*List\{($ksort),"(.*?)"\}(\s+\[.*?\])?)\s*(?=$kmaude_keywords_pattern)/sg)
    {
#	print "Matched: $&\n";

	$generated_code = "";
	
	# keep  syntax declaration
	my $syntax_item = $1;
	my $main_sort   = $2;
#	my $decl        = $3;
	my $list_sort   = $3;
	my $separator   = $4;
	my $attributes  = '[metadata ""]';
	$attributes     = $5 if defined $5;

	my $all = $main_sort;
	my $temp;
	
	if (!(defined $list_attributes_map{$separator}))
	{
            $attributes =~ s/metadata "/metadata "strict=() hybrid=() generated=() /s;
	    $list_attributes_map{$separator} = $attributes;
	}
	else 
	{
	    $attributes = $list_attributes_map{$separator};
	}

        my $gen_attributes = $attributes;
        $gen_attributes = s/metadata "/metadata " generated=() /s;

        my $list_attributes = $attributes;
        $list_attributes =~ s/metadata "/metadata " parser=() /s;

        my $parser_attributes = $gen_attributes;
        $parser_attributes =~ s/metadata "/metadata " parser=() /s;

	if (!(defined $declaration_map{$main_sort}))
	{
	    $generated_code .= "syntax $main_sort ::= List\{$list_sort\} $list_attributes\n";
            $generated_code .= "syntax List\{$list_sort\} ::= dummy$main_sort [metadata \"parser=() generated=()\"]\n";
#            $generated_code .= "\n\n//@ \\syntax\{\\nonTerminal\{\\sort\{$main_sort\}\}\}\{\\nonTerminal\{List\\\{\\sort\{$list_sort\},\\myquote\{$separator\}\\\}\}\}\{\}\n\n";
	    $generated_code .= "syntax $nelist$all ::= $list_sort [metadata \"generated=() parser=()\"] \n\t| $list_sort $separator $nelist$all $parser_attributes\n";
	    $generated_code .= "syntax $elist$all ::= .$main_sort [metadata \"generated=() parser=() latex=(renameTo \\\\ensuremath\{\\\\dotCt\{$main_sort\}\})\"] \n\t| $list_sort $separator $elist$all $parser_attributes \n\t| listify$all $list$all [metadata \"generated=() parser=()\" prec 0]\n";
	    $generated_code .= "syntax $list$all ::= $nelist$all  [metadata \"parser=() generated=()\"] | $elist$all [metadata \"parser=() generated=()\"] | $list_sort $separator $list$all $attributes\n";
	    
	    $generated_code  .= "\teq (listify$all(X$counter:$list_sort)) = (X$counter:$list_sort $separator .$main_sort) [metadata \"parser=() generated=()\"]\n"; $counter ++;
	    $generated_code  .= "\teq (listify$all(X$counter:$list_sort $separator NEL$counter:$nelist$all)) = (X$counter:$list_sort $separator listify$all(NEL$counter)) [metadata \"parser=() generated=()\"]\n\n"; $counter ++;
	    $generated_code  .= "\teq (listify$all(EL$counter:$list$all)) = (EL$counter) [metadata \"parser=() generated=()\" owise]\n"; $counter ++;
	    
	    # mark all as defined ..
	    $declaration_map{$main_sort} = "$list_sort:\"$separator\"";
	    $declared_list{"$list_sort:$separator"} = $main_sort;	    
	}
	elsif ("$list_sort:\"$separator\"" ne $declaration_map{$main_sort})
	{
	    die "[ERROR] [Duplicated list declaration for $main_sort. $main_sort is declared both as $list$declaration_map{$main_sort} and $list$all]";
	}

        if (! defined $constructors{"\"$separator\""})
        {
	    $generated_code .= "syntax ${list}List\{Bottom,\"$separator\"\} ::= ${nelist}List{Bottom,\"$separator\"\}  [metadata \"parser=() generated=()\"] | SemList\{Bottom,\"$separator\"\} [metadata \"parser=() generated=()\"] | Bottom $separator ${list}List\{Bottom,\"$separator\"\} $attributes\n";
	    $generated_code .= "syntax SemList\{Bottom,\"$separator\"\} ::= Bottom $separator SemList\{Bottom,\"$separator\"\}  $parser_attributes\n";
            $generated_code .= "syntax SemList\{Bottom,\"$separator\"\} ::=  .List\{\"$separator\"\} [metadata \"generated=()\"]\n";
            
	    $generated_code .= "syntax ${nelist}List\{Bottom,\"$separator\"\} ::= Bottom $separator ${nelist}List\{Bottom,\"$separator\"\}$parser_attributes\n";
 	    $generated_code .= "syntax ${nelist}List\{Bottom,\"$separator\"\} ::= Bottom [metadata \"parser=() generated=()\"] \n";
	    
            $constructors{"\"$separator\""} = "\"$separator\"";
        }
        
        # if (defined $constructor{\"$separator\"})
        # {
	$generated_code .= "  subsort ${list}List\{Bottom,\"$separator\"\} < $list$main_sort\n";
	$generated_code .= "  subsort ${nelist}List\{Bottom,\"$separator\"\} < $nelist$main_sort\n";
	$generated_code .= "  subsort SemList\{Bottom,\"$separator\"\} < $elist$main_sort\n";
	$generated_code .= "  eq .$main_sort = .List\{\"$separator\"\} [metadata \"parser=() generated=()\"]\n\n";
        # }

        my $subs = getSubSorts($list_sort);
	my $supers = getSuperSorts($list_sort);
	my @subs = @$subs;
	my @supers = @$supers;
	
#	print "SORT: $list_sort\nSUB: @subs\nSUPER: @supers\n\n";
	
#	print "MAP:\n";
#	while (my ($k, $v) = each (%declared_list))
#	{
#	    print "($k, $v)\n";
#	}
#       print "ENDMAP\n";

	
	my $sort2 = $main_sort; 

	foreach my $sort1 (@supers)
	{
	    if (defined $declared_list{"$sort1:$separator"})
	    {
		my $list1 =  $declared_list{"$sort1:$separator"};
#		$generated_code .= "subsort $main_sort < " . $declared_list{"$sort1:$separator"} . "\n";
		$generated_code .= "subsort $elist$sort2 < $elist$list1 \n";
		$generated_code .= "subsort $nelist$sort2 < $nelist$list1\n";
		$generated_code .= "subsort $list$sort2 <  $list$list1\n";
#		$generated_code .= "eq .$elist$list1 = .$elist$declaration_map{$sort2} [metadata \"parser=()\"]\n";
	    }
	}
	
	my $sort1 = $main_sort;
	foreach  $sort2 (@subs)
	{
	    if (defined $declared_list{"$sort2:$separator"})
	    {
		my $list2 = $declared_list{"$sort2:$separator"};		
#		$generated_code .= "subsort " . $declared_list{"$sort2:$separator"} . " < $main_sort \n";
		$generated_code .= "subsort $elist$list2 < $elist$sort1 \n";
		$generated_code .= "subsort $nelist$list2 < $nelist$sort1\n";
		$generated_code .= "subsort $list$list2 <  $list$sort1\n";
#		$generated_code .= "eq .$elist$declaration_map{$sort1} = .$elist$list2 [metadata \"parser=()\"]\n";
	    }
	}

	
	
	s/\Q$syntax_item\E/\n$generated_code/s;

#	print "Generated:\n$generated_code\n\n";
	
	
    }	

    # keys: lists sorts
    my $keys = join("|", keys %declaration_map);
#    
#    while ($temp =~ /(syntax\s+($keys)\s*::=\s*($keys))\s*\[\s*metadata.*?\]\s*(?=$kmaude_keywords_pattern)/sg)
#    {
#	my $syntax_item = $1;
#	my $sort1 = $2;
#	my $sort2 = $3;
#	
#	my $gen_code = "";
#	
#	$gen_code .= "subsort $elist$declaration_map{$sort2} < $elist$declaration_map{$sort1} \n";
#	$gen_code .= "subsort $nelist$declaration_map{$sort2} < $nelist$declaration_map{$sort1}\n";
#	$gen_code .= "subsort $list$declaration_map{$sort2} <  $list$declaration_map{$sort1}\n";
##	$gen_code .= "eq .$elist$declaration_map{$sort1} = .$elist$declaration_map{$sort2} [metadata \"generated=()\"]\n";
#
#        print "PROD: $syntax_item\nGEN: $gen_code\n\n";
#
#	s/\Q$syntax_item\E/$syntax_item\n\n$gen_code/s;
#    }
#    
    # iterate through syntax declarations
    while ($temp =~ /(syntax\s+(\S+)\s*::=(.*?(\s*\[\s*metadata.*?\])?))\s*(?=$kmaude_keywords_pattern)/sg)
    {
	# keep syntax declaration
	my $syntax_item = $1;
	my $main_sort   = $2;
	my $productions = $3;
	my $gen = "";
	
	# productions
	my @productions = ($productions =~ /(.*?\S.*?(?:\s\|\s|$))/gs);

	# iterate through productions
	foreach my $production (@productions)
	{
	    # Removing the | separator
	    $production =~ s/(\s)\|(\s)/$1$2/gs;
	    
	    # get all possible solutions
	    my $productions_gen = macrofy(gen_prod($keys, $production, $main_sort));
#	    print "PROD: $production\nGEN:$productions_gen\n\n";
	    
	    $gen .= "$productions_gen\n";
       	}
	
	s/\Q$syntax_item\E/$syntax_item\n\n$gen/s;	
    }
	    
    $_;
}




# Something ::= function #Id (Ids) {} 
# Ids |-> {#Id,","}
# macro function X1:#Id ( X2:NeList{#Id,","} ) {E:Stmt} = function X1:#Id ( listify{#Id,","}(X2:NeList{#Id,","}) {E:Stmt} 

sub gen_prod
{
    my $keys = shift;
    my $production = shift;
    my $main_sort = shift;
#    print "Start\n";
    

    my $pkeys_no = 0;
    my @prods = ();
    while ($production =~ /($keys)/sg) { $pkeys_no ++; push(@prods, $1); }
    
#    print "PKEYS: $pkeys_no\n";

    my @generated = ();
    if ($pkeys_no > 0)
    {
	if ($pkeys_no == 1)
	{
	    my @set = (); push(@set, 0);
	    push(@generated, generation($production, $main_sort, $pkeys_no, \@prods, \@set));
	}
	else
	{
	    if ($pkeys_no < 10)
	    {
		my $power = 2**$pkeys_no;	    
		
		foreach my $i (0.. ($power - 1))
		{
		    my @tmp = ();
		    my @set = ();
		    for(my $j = 0; $j < @prods; $j ++)
		    {
			if (isSet($j, $i))
			{
			    push(@tmp, $prods[$j]);
			    push(@set, $j);
			}
		    }
		    push(@generated, generation($production, $main_sort, $pkeys_no, \@tmp, \@set));
		}		
	    }
	}
	
	my $tmp = $production;
	
	$tmp =~ s/\[\s*?metadata.*?\]\s*$//sg;
	my $pkeys = join("|", @prods);
	    
	if ($tmp !~ /^\s*($ksort)\s*$/s && "@prods" !~ /^\s*$/)
	{
	    foreach my $i (0 .. ($pkeys_no - 1))
	    {
	    
	    my $left = $tmp;
	    my $right = $tmp;
	    
            # syntax Stmt ::= function Id(Ids) {Stmts}
	    
	    # Ids ::= List{#Id, ","}
	    # Stmts ::= List{Stmt,""}
	    
	    # macro function X:Id(Y:SyntacticList{#Id,","}) {Z:Stmts} = 
	    #    function X:Id(listify(Y:SyntacticList{#Id,","})) {Z:Stmts} [metadata "generated=()"]
	    
	    my $count = -1;
	    
	    $right =~ s/(?<![0-9a-zA-Z`])($ksort)/
	    {
		$counter ++; my $sort = $1;
                if ($sort =~ m!($pkeys)!sg) {
                  $count ++;
                  if ($count==$i) {
		    "(listify$1(X$counter:$nelist$1))";
		  } else {
                    "X$counter:$1";
                  }
                } else {
		    "X$counter:$1";
		}
	    }
	    /sge;
	    
	    $right =~ s/`/ /sg;
	    
	    $left = $right;
	    $left =~ s/listify[^(]*//sg;
	    
	    
#	    print "Prod: $production\nPKEYS: $pkeys\nPRODS: @prods\nTMP: $tmp\n";
#	    print "macro ($left) = ($right) [metadata \"generated=() parser=()\"]\n";
	    push(@generated, "macro ($left) = ($right) [metadata \"generated=() parser=()\"]");
	    }
	}
    }
 
    \@generated;
}

sub contains
{
    my $set = shift;
    my $number = shift;
    my @set = @$set;
    
    foreach my $s (@set)
    {
	return 1 if $s == $number;
    }
    
    return 0;
}

sub generation
{
    my $production = shift;
    my $main_sort = shift;
    my $pkeys_no = shift;
    my $array = shift;
    my $set = shift;
    
    my @array = @$array;
    my $out = "";
    
#    print "ARRAY: @array\n" if @array < $pkeys_no;
    if (@array != 0)
    {
#	print "ARRAY: @array\n";
	my $mkeys = join("|", @array);
	
    	
	my $temp_prod = $production;
	# remove attributes
	$temp_prod =~ s/\[\s*metadata.*?\]\s*$//sg;

	
	# stop if terminals not included in production
	my $tmp_prod = $temp_prod;
	$tmp_prod =~ s/(?<![0-9a-zA-Z`])($ksort)\b//sg;
	return "" if  $tmp_prod =~ /^\s*$/s;

	my $ttemp = $temp_prod;
	$ttemp =~ s/(?<![0-9a-zA-Z`])($ksort)/{ my $t = $1; $counter ++; $t !~ m!($nelist|$elist|$mkeys)! ? getvar($t) . "$counter:$t" : "$t" ; }/sge;
	my $left = $ttemp;
	my $right = $ttemp;
	$counter ++;
	
	# for syntax generation
	my $count = 0;
	$temp_prod =~ s/($mkeys)/
	{
	    $count = 0;
	    my $mk = $1;
	    while ($count < $pkeys_no)
	    {
		if (contains($set, $count) == 1)
		{
		    $mk = "";
		}
		$count ++;
	    }
	    $mk;
	}/gse;
	
	# left = for macro generation
	$count = 0;
	$left =~ s/($mkeys)/
	{
	    $count = 0;
	    my $mk = $1;
	    while ($count < $pkeys_no)
	    {
		if (contains($set, $count) == 1)
		{
		    $mk = "";
		}
		$count ++;
	    }
	    $mk;
	}/gse;
	
	# right = for macro generation
	$count = -1;
	$right =~ s/\b($mkeys)\b/
	{
	    $count ++;
	    my $mk = $1;
	    # extract separator
	    my $nk = "";
	    $nk = $& if ($declaration_map{$mk} =~ m!(\".*?\")!sg); # do we have a default separator for lists? :-"
	    ($declaration_map{$mk} =~ m!(\".*?\")!sg); # isn't perl wonderful ? :-D

	    $count = 0;
	    while ($count < $pkeys_no)
	    {
		if (contains($set, $count) == 1)
		{
		    $mk = ".List{$nk}";
		}
		$count ++;
	    }
	    $mk;
#	    print "SeP: |$nk|   PPP: " . ($declaration_map{$mk} =~ m!(\".*?\")!sg) . "\n";
#	    contains($set, $count) == 1 ? ".List{$nk}" : $mk ;
	}/gse;
	

#	print "Set: @$set\n";
#	print "TMP: $temp_prod\nLEFT: $left\nRIGHT:$right\n\n";

	$left  =~ s/`//sg;
	$right =~ s/`//sg;
	
	$out .= "\tsyntax $main_sort ::= $temp_prod [metadata \"parser=() generated=()\"]\n";
	$out .= "\tmacro ($left) = ($right) [metadata \"parser=() generated=()\"]\n\n";
    }
    
    return $out;
}


sub isSet
{
    my $bit = shift;
    my $no  = shift;
    
    ($no >> $bit) & 1;
}


sub getvar
{
    local $_ = shift;
    s/^#//;
    $_;
}


sub macrofy
{
    my $v = shift;
    my @v = @$v;
    my @all = ();
    foreach(@v)
    {
	push(@all, $_) if $_ !~ /^\s*$/;
    }
    
    return "" if @all == 0;
    
    "@all";
}

1;
