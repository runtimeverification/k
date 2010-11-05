#!/usr/bin/perl
use Getopt::Long;

#
# Turn off auto abbreviations, so we can control them if we want to.
#
Getopt::Long::Configure("no_auto_abbrev");

#
# Options can be specified here. "exec|e" allows command-line args of
# the form -e, -exec, --exec, and --e.
#
# Current options are:
# -- default         Specify which analysis is the default analysis
#
GetOptions("default|d=s"=>\$default_analysis,
           "help|?"=>\$help_flag,
		   "output|o=s"=>\$output_flag);

#
# Check to see if the user wants a usage message -- if so, print one and exit
#
if ($help_flag) {
  usage();
  exit;
}

#
# Grab back the name of the program file -- this is needed for all cases
# except --help, which is handled above (and which doesn't check)
#
if ($ARGV[0]) {
  $c_prog = $ARGV[0];
} else {
  print STDERR "Error: A C program file must be specified on the command line.\nUse --help or -? for usage.\n";
  exit;
}

if ($output_flag) {
	
} else {
	$output_flag = "$c_prog.embed";
}

#
# Verify the specified program exists.
#
if (! (-e $c_prog)) {
  print STDERR "Source file $c_prog not found\n";
  exit;
}

#
# Open the file; we will process it line by line, looking for our
# annotation comments.
#
open CSOURCE, "< $c_prog" or die "Cannot open file $c_prog\n";

#
# Open the destination file name.
#
open CDEST, "> $output_flag" or die "Cannot open output file $output_flag\n";

# Print our fake function decl
print CDEST "void fslAnnotation(char*, ...);\n";


#
# Set up the lists we will use to track pre- and post-conditions.
#
@preconds = ();
@postconds = ();
@modifies = ();
@tinvariants = ();

#
# $funflag keeps track of whether we should be looking for the start of a function;
# this is used after finding pre- or post-condition comments so we know where to
# insert the actual pre- and post-condition code.
$funflag = 0;

#
# Now, process the C source file
#
my $linenum = 0;
while ($line = <CSOURCE>) {
$linenum++;
  # Check for annotation comments. For now, keep it simple -- assume only one annotation comment 
  # on any given line. Assertions and assumptions are replaced inline, since they could be embedded
  # in the middle of code, like <code> /*@ assume */ <more code>. Conditions with the system defined
  # should be checked for first, since if not the regex for conditions with no system defined will
  # also match because the : is optional, meaning the system would be seen as part of the condition.


  # $ppflag marks if we are scanning a pre- or post-condition. Since they are always before a function
  # declaration or definition, this lets us know that if we find a { or ; on the line after we stopped
  # scanning conditions that this is the ; or { at the end of the function header.
  $ppflag = 0;

  # Keep track of changed output text.
  $outline = "";

  
# int fslAnnotation __attribute__ ((visibility ("protected"))); fslAnnotation = 0;

  # Asserts, /*@ and //@ style comments, no system defined
  #$var =~ s/([CHARLIST])/\\$1/g;
	
	my @vars = ();
	my @atvars = ();
	#print "$line\n";
	while ($line =~ m/(\@(\w+))\b/g) {
		#print "Found '$&'\n";
		push(@vars, $2);
		push(@atvars, "\"$1\"");
		#Next attempt at character " . pos($string)+1 . "\n";
	}
	@vars = zip2(@atvars, @vars);
	my $varstr = join(', ', @vars);
	if ($varstr){
		$varstr = ", $varstr";
	}
	if ($line =~ s/\/\/\@\s*assert(\:?)\s*(.*)$/fslAnnotation("assert ($2)"$varstr);/i) {
	} elsif ($line =~ s/\/\/\@\s*assume(\:?)\s*(.*)$/fslAnnotation("assume ($2)"$varstr);/i) {
	} elsif ($line =~ s/\/\/\@\s*invariant(\:?)\s*(.*)$/fslAnnotation("invariant ($2)"$varstr);/i) {
	} elsif ($line =~ s/\/\/\@\s*pre(\:?)\s*(.*)$/fslAnnotation("pre ($2)"$varstr);/i) {
	} elsif ($line =~ s/\/\/\@\s*post(\:?)\s*(.*)$/fslAnnotation("post ($2)"$varstr);/i) {
	}
  

  # If we didn't write anything into $outline yet, just copy in the $line, so we can always just
  # output $outline. This will usually be the case (it will be on any standard lines of C code).
  if ($outline eq "") {
    $outline = $line;
  }

  # Don't output pre- and post-condition comment lines. Since we are adding the pre- and post-conditions
  # to the functions, dropping the comment lines helps us keep the same line numbers as we start with; only
  # the first line number for the function header should change.
  #if ($ppflag == 0) {
    print CDEST $outline;
  #}
}

print CDEST "\n";

# Perl trim function to remove whitespace from the start and end of the string
sub trim($)
{
        my $string = shift;
        $string =~ s/^\s+//;
        $string =~ s/\s+$//;
        return $string;
}
# Left trim function to remove leading whitespace
sub ltrim($)
{
        my $string = shift;
        $string =~ s/^\s+//;
        return $string;
}
# Right trim function to remove trailing whitespace
sub rtrim($)
{
        my $string = shift;
        $string =~ s/\s+$//;
        return $string;
}
# from http://stackoverflow.com/questions/38345/is-there-an-elegant-zip-to-interleave-two-lists-in-perl-5
# interleaves two lists together 
sub zip2 {
    my $p = @_ / 2; 
    return @_[ map { $_, $_ + $p } 0 .. $p - 1 ];
}


#
# Usage message 
#
sub usage()
  {
    print STDERR << "EOF";

embed embeds preconditions, postconditions, assertions, and assumptions into
a C source file, which can then be processed using an extension to CIL.

usage: $0 [flags] prog.c

flags include:
--default=analysis    specify the default analysis (for instance, UNITS)
--help                display usage info (which you are now reading) and exit
--output=file         output gets saved here

short forms include:
-d       =        --default
-o       =        --output
-?       =        --help

EOF
}

