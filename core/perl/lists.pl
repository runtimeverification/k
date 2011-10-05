#!/usr/bin/env perl


use strict;
use warnings;
use POSIX;

my $ksort = "[A-Z#][A-Za-z0-9\\`\\+\\?\\!#]*(?:\\{[A-Z#][A-Za-z0-9\\`\\+\\?\\!]*\\})?";
my @kmaude_keywords = qw(context rule macro eq ceq configuration op ops syntax kvar sort sorts subsort subsorts including kmod endkm mb tags);
my $kmaude_keywords_pattern = join("|",map("\\b$_\\b",@kmaude_keywords));


my $nelist = "SyntacticList";
my $elist  = "List";
my $list   = "TranslationList";

my $counter = 7;

my %declaration_map = ();
my %constructors = ();

sub solve_lists
{
    local $_ = shift;
    my $temp = $_;
    
    # store generated code
    my $generated_code = "";

    
    # presupunem: | syntax Ids ::= List{#Id, ","} [attributes] |
    # iterate through syntax declarations
    while ($temp =~ /(syntax\s+($ksort)\s*::=\s*($elist)\{($ksort),"(.*?)"\}(\s+\[.*?\])?)\s*(?=$kmaude_keywords_pattern)/sg)
    {
#	print "Matched: $&\n";

	$generated_code = "";
	
	# keep  syntax declaration
	my $syntax_item = $1;
	my $main_sort   = $2;
	my $decl        = $3;
	my $list_sort   = $4;
	my $separator   = $5;
	my $attributes  = '[metadata ""]';
	$attributes     = $6 if defined $6;

        my $parser_attributes = $attributes;
        $parser_attributes =~ s/metadata "/metadata "parser=() /s;
	
	my $all = "\{$list_sort,\"$separator\"\}";
	my $temp;
	
	if (!(defined $declaration_map{$main_sort}))
	{
            $generated_code .= "\tsort $main_sort\n";
            $generated_code .= "\tsort $elist$all\n";
            $generated_code .= "\tsort $list$all\n";
            $generated_code .= "\tsort $nelist$all\n";
	    $generated_code  .= "\tsubsort $list$all < $main_sort\n";
	    $generated_code  .= "\tsubsort  $list_sort < $nelist$all\n";
	    $generated_code  .= "\top _$separator"."_ :  $list_sort $nelist$all -> $nelist$all $parser_attributes\n";
	    $generated_code  .= "\top .$elist$all : -> $elist$all\n";
	    $generated_code  .= "\top _$separator"."_  : $list_sort $elist$all -> $elist$all $attributes\n";
	    $generated_code  .= "\tsubsorts $nelist$all $elist$all < $list$all\n";
	    
	    $generated_code  .= "\top listify$all"."_ : $list$all -> $elist$all [metadata \"parser=()\"]\n";
	    
	    $generated_code  .= "\teq (listify$all(EL$counter:$elist$all)) = (EL$counter) [metadata \"parser=()\"]\n"; $counter ++;
	    $generated_code  .= "\teq (listify$all(X$counter:$list_sort)) = (X$counter:$list_sort $separator .$elist$all) [metadata \"parser=()\"]\n"; $counter ++;
	    $generated_code  .= "\teq (listify$all(X$counter:$list_sort $separator NEL$counter:$nelist$all)) = (X$counter:$list_sort $separator listify$all(NEL$counter)) [metadata \"parser=()\"]\n\n"; $counter ++;
	    
	    # mark all as defined ..
	    $declaration_map{$main_sort} = $all;
	}
	elsif ($all ne $declaration_map{$main_sort})
	{
	    die "[ERROR] [Duplicated list declaration for $main_sort. $main_sort is declared both as $list$declaration_map{$main_sort} and $list$all]";
	}

        if (! defined $constructors{"\"$separator\""})
        {
            if (! scalar keys(%constructors)) {
              $generated_code .= "  sort Bottom\n";
            }
            $generated_code .= "  sort $list\{Bottom,\"$separator\"\}\n";
            $generated_code .= "  sort $elist\{Bottom,\"$separator\"\}\n";
            $generated_code .= "  sort $nelist\{Bottom,\"$separator\"\}\n";
            $generated_code .= "subsort $nelist\{Bottom,\"$separator\"\} $elist\{Bottom,\"$separator\"\} < $list\{Bottom,\"$separator\"\}\n";
            $generated_code .= "op _$separator"."_ : Bottom  $elist\{Bottom,\"$separator\"\} -> $elist\{Bottom,\"$separator\"\} $attributes\n";
            $generated_code .= "op .\{\"$separator\"\} : ->  $elist\{Bottom,\"$separator\"\}\n";
            $generated_code .= "op _$separator"."_ : Bottom  $nelist\{Bottom,\"$separator\"\} -> $nelist\{Bottom,\"$separator\"\} $parser_attributes\n";
            $generated_code .= "subsort Bottom < $nelist\{Bottom,\"$separator\"\}\n";
            $constructors{"\"$separator\""} = "\"$separator\"";
        }
        
        # if (defined $constructor{\"$separator\"})
        # {
            $generated_code .= "  subsort $list\{Bottom, \"$separator\"\} < $list$declaration_map{$main_sort}\n";
            $generated_code .= "  subsort $nelist\{Bottom, \"$separator\"\} < $nelist$declaration_map{$main_sort}\n";
            $generated_code .= "  subsort $elist\{Bottom, \"$separator\"\} < $elist$declaration_map{$main_sort}\n";
            $generated_code .= "  eq .$elist$declaration_map{$main_sort} = .\{\"$separator\"\}";
        # }

	
	s/\Q$syntax_item\E/\n$generated_code/s;

#	print "Generated:\n$generated_code\n\n";
    }	

    # keys: lists sorts
    my $keys = join("|", keys %declaration_map);
    
    # print "Got Here!\n$temp\n";
    while ($temp =~ /(syntax\s+($keys)\s*::=\s*($keys))\s*\[\s*metadata.*?\]\s*(?=$kmaude_keywords_pattern)/sg)
    {
	my $syntax_item = $1;
	my $sort1 = $2;
	my $sort2 = $3;
	
	my $gen_code = "";
	
	$gen_code .= "subsort $elist$declaration_map{$sort2} < $elist$declaration_map{$sort1} \n";
	$gen_code .= "subsort $nelist$declaration_map{$sort2} < $nelist$declaration_map{$sort1}\n";
	$gen_code .= "subsort $list$declaration_map{$sort2} <  $list$declaration_map{$sort1}\n";
	$gen_code .= "eq .$elist$declaration_map{$sort1} = .$elist$declaration_map{$sort2}\n";

        #print "PROD: $syntax_item\nGEN: $gen_code\n\n";

	s/\Q$syntax_item\E/$syntax_item\n\n$gen_code/s;
    }
    
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
	    my $productions_gen = gen_prod($keys, $production);
	    my $macros = macrofy($productions_gen); # =))))))
#	    print "PROD: $production\nGEN:$macros\n\n";
	    $gen .= "$macros\n";
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
	    push(@generated, generation($production, \@prods));
	}
	else
	{
	    if ($pkeys_no < 30)
	    {
		my $power = 2**$pkeys_no;	    
		
		foreach my $i (0.. ($power - 1))
		{
		    my @tmp = ();
		    for(my $j = 0; $j < @prods; $j ++)
		    {
			push(@tmp, $prods[$j]) if isSet($j, $i);
		    }
		    push(@generated, generation($production, \@tmp));
		}
	    }
	}
    }
 
    \@generated;
}

sub generation
{
    my $production = shift;
    my $array = shift;
    my @array = @$array;
 
    if (@array == 0)
    {
	    my $temp_prod = $production;

	# remove attributes
	$temp_prod =~ s/\[\s*metadata.*?\]\s*$//sg;
	
#	$temp_prod =~ s/($ksort)/{ my $t = $1; $counter ++; $t !~ m!($nelist|$elist|$list)! ? getvar($t) . "$counter:$t" : "$t" ; }/sge;
	
#	return $temp_prod;
	return "\n";
    }
	
    
    my $mkeys = join("|", @array);
    
    my $temp_prod = $production;

    # remove attributes
    $temp_prod =~ s/\[\s*metadata.*?\]\s*$//sg;
	
    $temp_prod =~ s/($ksort)/{ my $t = $1; $counter ++; $t !~ m!($nelist|$elist|$list|$mkeys)! ? getvar($t) . "$counter:$t" : "$t" ; }/sge;
    $counter ++;
	
    # generating  macro
    my $left  = $temp_prod;
    my $right = $temp_prod;
    
    my $c1 = $counter;
    my $c2 = $counter;

    # code generation!
    $left  =~ s/($mkeys)/{ my $sort = "$nelist$declaration_map{$1}"; my $decl = "X$c1:$sort"; $c1 ++; $decl; }/sge;
    $right =~ s/($mkeys)/{ my $sort = $declaration_map{$1}; my $decl = "listify$sort(X$counter:$nelist$sort)"; $c2 ++; $decl; }/sge;
    $counter += ($c1 - $counter);
 
#    print "ARRAY: @array\n($left) = ($right)\n\n";
    
    
    "($left) = ($right) [metadata \"parser=()\"]\n";
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
    
    "macro " . join(" macro ", @all);
}

1;
