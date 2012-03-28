#!/usr/bin/env perl

use strict;
use warnings;

my $path = File::Spec->catfile((File::Basename::fileparse($0))[1], 'perl', 'common_functions.pl');
require $path;


my $ksort = "[A-Z#][A-Za-z0-9\\\\+\\?\\!#]*(?:\\{[A-Z#][A-Za-z0-9\\\\+\\?\\!]*\\})?";
my @kmaude_keywords = qw(context rule macro eq ceq configuration op ops syntax kvar sort sorts subsort subsorts including kmod endkm mb tags);
my $kmaude_keywords_pattern = join("|",map("\\b$_\\b",@kmaude_keywords));



# $sort -> $array of subsorts
my %subsorts_map   = ();

# $sort -> $array of supersorts
my %supersorts_map = ();


#########################
# test
################

sub test
{
    local $_ = shift;
    
#    my ($map1, $map2) = sorting($_);
    
    my $sort = "Exp";
    print "\n\n";

    my $ss = getSuperSorts("$sort");
    print "$sort(SS): @{$ss} \n";
    $ss = getSubSorts("$sort");
    print "$sort(ss): @{$ss} \n";
    $ss = getAllSuperSorts("$sort");
    print "$sort(ALLSS): @{$ss} \n";
    $ss = getAllSubSorts("$sort");
    print "$sort(ALLss): @{$ss} \n";
}

#######################
# end test
#######################



######################
# main
######################


# return the "most" subsorts
sub getSubSorts
{
    my $sort = shift;
    my $map = \%subsorts_map;
    
    my $arr = get_recursive_relation($sort, $map);
    my @arr = defined $arr && @{$arr} ?  set_(@{$arr}) : ();
    
    \@arr;
}

# return the "most" supersorts
sub getSuperSorts
{
    my $sort = shift;
    my $map = \%supersorts_map;
    
    my $arr = get_recursive_relation($sort, $map);
    my @arr = defined $arr && @{$arr} ?  set_(@{$arr}) : ();
    
    \@arr;
}


# return all subsorts
sub getAllSubSorts
{
    my $sort = shift;
    my $map = \%subsorts_map;
    
    my $arr = recursive_sorting($sort, $map);
    my @arr = defined $arr && @{$arr} ?  set_(@{$arr}) : ();

    \@arr;
}

# return all subsorts
sub getAllSuperSorts
{
    my $sort = shift;
    my $map = \%supersorts_map;
    
    my $arr = recursive_sorting($sort, $map);
    my @arr = defined $arr && @{$arr} ?  set_(@{$arr}) : ();

    \@arr;
}


#########################
# end main 
#########################


#########################
# utils
#########################



# iterate through syntax and retrieve sorts and relationships among them
sub sorting
{
    local $_ = shift;
 
    s/\[\s*metadata.*?\]/Freeze($&, "MEDATA")/sge;
    
    while (/(syntax\s+(\S+)\s*::=(.*?))(\s*)(?=$kmaude_keywords_pattern)/sg)
    {
	# keep  syntax declaration
	my $syntax_item = $1;
	my $main_sort   = $2;
	my $productions = $3;
	
	# productions
	my @productions = ($productions =~ /(.*?\S.*?(?:\s\|\s|$))/gs);

	foreach my $production (@productions)
	{
	    $production =~ s/MEDATA\S+//s;
	    $production =~ s/\s*(?<!`)\|\s*//s;
	    
            # print "\nPRODUCTION: $production  ";
	    if ($production =~ /^\s*($ksort)\s*$/)
	    {
              # print "SUBSORTS: $1 < $main_sort";
		# !!! store both subsorts and supersorts
		store($main_sort, $1);
	    }
	}
    }
    
    return (\%subsorts_map, \%supersorts_map);
}

# store both subsorts and supersorts
# this is called by sorting
sub store
{
    my $sort = shift;
    my $production_sort = shift;
    
    if (defined $subsorts_map{$sort})
    {
	# append subsorts to current sort
	my @slist = @{$subsorts_map{$sort}};
	push(@slist, $production_sort);
	$subsorts_map{$sort} = \@slist;

    }
    else
    {
	# subsorts
	my @slist = ();
	push(@slist, $production_sort);
	$subsorts_map{$sort} = \@slist;	
    }
    
    if (defined $supersorts_map{$production_sort})
    {
	# append supersorts to current sort
	my @slist = @{$supersorts_map{$production_sort}};
	push(@slist, $sort);
	$supersorts_map{$production_sort} = \@slist;
    }
    else
    {
	# super sorts
	my @slist = ();
	push(@slist, $sort);
	$supersorts_map{$production_sort} = \@slist;	
    }
}



# return an array of ALL sub/super sorts for a given sort
# and a hash of relations
sub recursive_sorting
{
    my $sort = shift;
    my $map_ref = shift;

    my $ss_ref = get_direct_ss($sort, $map_ref);
    my @ss_ref = @$ss_ref;
    my @temp_sorts = ();
    foreach my $ss (@ss_ref)
    {
	push(@temp_sorts, $ss);
	my $tmp = recursive_sorting($ss, $map_ref);
	if (defined $tmp)
	{
	    my @tmp = @$tmp;
	    push(@temp_sorts, @tmp);
	}
    }
 
    @temp_sorts ? \@temp_sorts : undef;
}


# return an array of sub/super sorts for a given sort
# and a hash of relations
sub get_recursive_relation
{
    my $sort = shift;
    my $map = shift;
   
#    print "SORT: $sort\n\n";
    my @results = ();
    my $tmp = recursive_sorting($sort, $map);
    
    if (defined $tmp)
    {
	my @tmp = @$tmp;
	my @temp = ();
	my %map = %$map;

	
	for(my $i = 0; $i < @tmp; $i ++)
	{
	    if (defined $map{$tmp[$i]} )
	    {
		push(@temp, $tmp[$i]) if !(@{$map{$tmp[$i]}} > 0);
	    }
	    else
	    {
		push(@temp, $tmp[$i]);
	    }
	}

	return \@temp;
    }

    undef;
}

# return direct subsortations
sub get_direct_ss
{
    my $sort = shift;
    my $map_ref = shift;
    my %map = %$map_ref;
    
    my @empty = ();
    return \@empty if !(defined $map{$sort});
    
    return $map{$sort};
}


# print map: $sort -> $array_of_sorts
sub display_map
{
    my $map_ref = shift;
    my %map = %$map_ref;
    while (my ($key, $value) = (each %map))
    {
	my @vector = @$value;
	print "$key: @vector\n";
    }
}

# get set-like array from another array
# get rid of duplicates
sub set_
{
    if (@_)
    {
	my %map = map { $_ => 1 } @_;
	return keys %map;
    }
    
    ();
}


1;
