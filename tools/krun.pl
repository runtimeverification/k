#!/usr/bin/perl -w
use warnings;
use strict;
use XML::Parser;

# maude path
my $maude_path = "maude";

# input maude file
my $input_file = "?";

# input maude
my $input = "";

# output content
my $output = "";

# output file
my $output_file = "temp.output";

# error file
my $error_file = "error.output";

# list of labels with one argument
my @one_arg_list = ();

# list of arguments 
my @arg_list = ();

###################
# main            #
###################

# process arguments
foreach (@ARGV)
{
    if ($input_file eq "?")
    {
	$input_file = $_;
    }
}


# checkings
terminate("No input file given.") if ($input_file eq "?");
terminate("The file $input_file doesn't exists.") if !(-e $input_file);

# Get input commands
$input = get_file_content($input_file);

# Run maude over the input file
$output = run_maude("Running maude...", 
		    "$input",
		    "\nquit");
# Get output
local $_ = get_file_content("out"); 

# Step: < cell >  goes to <cell>
s/<(\/?)\s+(.*?)\s+>/<$1$2>/g;


# Step: Id label(.List{K}) goes to label
s/[a-zA-Z_]+\s+(.+?)\(\.List{K}\)/$1/g;

# Step: label(.List{K}) goes to label
s/\s([a-zA-Z_0-9]+?)\(\.List{K}\)/ $1/g;

# Step: format configuration
s!<\s*(.+?)\s*>\s*(.+?)\s*<\s*\/\s*\1>\s*!my $temp = formatXML("<$1>$2</$1>");"\n$temp\n"!gse;


# Step: infix ~> mixfix   

# "Small"-step : replace '_`,_(one_argument)with one_argument
detect_list_labels($_);

my $tmp = $_;
foreach my $t (@one_arg_list)
{
    my $replacement = process_special_label($t);
    $tmp =~ s/\Q$t\E/$replacement/;
}

$_ = $tmp;

# "Small"-step: rebuild mixfix
my $rest = $_;
while (1)
{
    # get labels and arguments
    my $temp = getFirstLabel($rest);
    
    # stop if there are no labels left
    last if (!defined($temp));
    
    print "Temp: $temp\n";
    # replace old labels with processed labels
    s/(\Q$temp\E)/my $tmp = rew($temp);print "Tmp: $tmp\n";"$tmp"/se;
    
    # loop, but move forward :-)
    $rest =~ s/(\Q$temp\E)//;
}

# Step: replace .List{Sort} -> .
s/\.List\{[A-Za-z_]*\}/\./g;

print;

clean();

####################
# subroutines      #
####################

sub process_special_label
{
    local $_ = shift;
    
    if (/('.*?[^`])[\(,]/)
    {
	my $label = $1;
	my $temp = $_;
	$temp =~ s/\Q$1\E//;
	$temp =~ s/^\(//;
	$temp =~ s/\)$//;
	get_args_list($temp);

	return "@arg_list";
#	foreach (@arg_list)
#	{
#	    $label =~ s/_/$_/;
#	}

#	print "TO RETURN: $label\n";
#	$label =~ s/`[\.,\s]+_//;
#	print "RETURN: $label\n";
#	
#	return $label;
    }
    
    $_;
}
# collect all the labels with one argument
sub detect_list_labels
{
    local $_ = shift;

    my $temp;
    my $label;
    my $count;
#    while (/('[^']*[^`])\(/g)
    while (/('.*?[^`])[\(,]/g)
    {
	$label = $1;
	$temp = substr $_, length($`);
	$temp = getFirstLabel($temp);
	$temp =~ s/'.*?[^`](?=\()//;
	$temp =~ s/^\(//;
	$temp =~ s/\)$//;
	get_args_list($temp);
	# print "ARGS: @arg_list\n";

	$count = ($label =~ tr/_/_/);

	if ($count > scalar(@arg_list) )
	{
	    push(@one_arg_list, "$label($temp)");
	}
    }
}

# No of '(' - no of ')' - used to parse arguments
sub paranthesis_delta
{
    local $_ = shift;
    
    my $count = 0;
    my $quoted;

    while (/(.)/g)
    {
	$quoted = 0;
	$quoted = 1 if ((substr $`, -1, 1) eq "`");
	$count++ if ($1 eq "(" && !$quoted);
	$count-- if ($1 eq ")" && !$quoted);
    }
    
    $count;
}

# return a list of arguments
sub get_args_list
{
    local $_ = shift;

    @arg_list = ();
    my @args = split(/(?=[^`]),,/, $_);
    
    my $temp = "";
    foreach (@args)
    {
	$temp .= $_;
	if (paranthesis_delta($temp) == 0)
	{
	    push(@arg_list, $temp);
	    $temp = "";
	}
	else
	{
	    $temp .= ",,";
	}
    }
}

# rewrite each _ with its coresponding argument
sub rew
{
    local $_ = shift;
    
    while (/('([^']*?[^`])\(([^']*[^`])\))/)
    {
	my $label = $2;
	my $arguments = getFirstLabel($1);
	my $temp = $arguments;
	$arguments =~ s/\Q'$label\E//;
	$arguments =~ s/^\(//;
	$arguments =~ s/\)$//;
	my @args = split(/,,/, $arguments);
	foreach(@args)
	{
#	    $label =~ s/_/ $_ / if $_ !~ /\(.*\)/;
#	    $label =~ s/_/$_/ if /\(.*\)/;
	    $label =~ s/_/ $_ /;
	}

	s/\Q$temp\E/$label/;
    }

    # remove all quotes
    s/`//g;
    
    # remove transitions ~>
    s/~>//g;

    return $_;
}


# get next label (label + full label body)
sub getFirstLabel
{
    local $_ = shift;
    my $label;

#    print "Process: $_\n";
    
    # return undef if no label detected
    # $label if (!/('.*?[^`])[\(,]/);
    undef if (!/('.*?[^`])[\(,]/);

    # compute the full body of the label
    my $count = 1;
    my $last = "";
    my $labelname = "";
    if (/('.*?[^`][\(,])/)
    {
	$last = substr $_, length($`) + length($&);
	$label = $1;
    }


    my $quoted;
    while ($last =~ /([^\n])/g)
    {	
	$quoted = 0;
	$quoted = 1 if ((substr $`, -1, 1) eq "`");
	$count++ if ($1 eq "(" && !$quoted);
	$count-- if ($1 eq ")" && !$quoted);
	$label .= $1;
	last if $count == 0;
    }
    
    $label;
}



# input: a configuration
# output: an xml indentation 
my $indent = "    ";
sub formatXML
{
    local $_ = shift;
    
    # eliminate whitespaces around cells
    s/\s+(<\/?.+?>)\s+/$1/sg;

    # increase indentation
    $indent .= "    ";

    # format
    s!<\s*(.+?)\s*>\s*(.+?)\s*<\s*\/\s*\1>\s*! my $cell = $1; my $content = formatXML($2); $content =~ s/^\s+//;"\n$indent<$cell>\n$indent    $content\n$indent<\/$cell>"!gse;

    # decrease indentation
    $indent =~ s/    $//; 

    # eliminate empty lines
    s/^\n//g;

    return $_;
}

# termination generic subroutine
sub terminate
{
    print "Termination occured.\nError: " . (shift) . "\n";
    exit(1);
}


# get content of a file
sub get_file_content
{
    my $filename = shift;

    open FILE, "<", $filename or die "Could not open $filename:\n$!";
    my @input = <FILE>;
    close FILE;

    return "@input";
}


# Running Maude (cross platform)
sub run_maude 
{
    # prepare maude output
    my ($message,@commands) = @_;
#    print "Commands: @commands\n";
    print "$message\n";
    my $output_file = "temp";
    open FILE,">",$output_file or die "Cannot create $output_file\n";
    print FILE "\n@commands\n";
    close FILE;

    # call maude
    my $status = system("$maude_path -no-banner -no-wrap $output_file >out 2>$error_file");
    if (($status >>= 8) != 0)
    {
        terminate ("Failed to run maude. Exit status $status.\n");
    }

    unlink($output_file);
}


sub clean
{
    unlink("out");
    unlink($output_file);
    unlink($error_file);
}
