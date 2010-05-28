#!/usr/bin/perl
use strict;
use File::Basename;
use File::Spec;

# next subroutine prints the usage message;
# $0 is initially bound to the program name, as typed
sub usage {
    print "
usage: $0 <source_file>[.kmaude] [<module_name>]

  If <module_name> is not specified, it is asumed to be allcaps(<source_file>).
  <source_file> must define directly or indirectly (via loading) module <module_name>.
  Module <module_name> should contain the entire definition of the language.
  Output is printed in <source_file>-compiled.maude.

  If an error occurs in the compilation process (including any Maude warnings),
  the script will stop, displaying the input, the (possibly partially) generated output,
  and the error/warning messages reported by Maude.

" ;
}

# prints the usage message whenever the program is not called with one or two arguments,
# or whenever it is called with the help option (-h, --h, -help, --help, etc.)
if ($#ARGV < 0 || $#ARGV > 1 || $ARGV[0] =~ /^--*(h|help)$/) {
    usage;
    exit;
}

# adds the extension ".kmaude" to <source_file> in case it didn't have it
# it does not remove any other extension that it may have had
# for example, lang.syntax becomes lang.syntax.kmaude
my $language_file = (($ARGV[0] =~ /^(.*)\.kmaude$/) ? $1 : $ARGV[0]);

my $k_tools_dir = (File::Basename::fileparse($0))[1];
my $maudify  = File::Spec->catfile($k_tools_dir,"maudify.sh");
my $kcompile = File::Spec->catfile($k_tools_dir,"kcompile.sh");

# maudify the file "$language_file.kmaude", as well as all other reachable .kmaude files
maudify($maudify,"$language_file.kmaude");

system "$kcompile $language_file.maude";

sub maudify {
    my ($maudify,$kmaude_file) = @_;
    open FILE, "<", $kmaude_file or die "Cannot open file $kmaude_file; exiting\n";
    my @lines = <FILE>;
    close FILE;
    print "Maudifying $kmaude_file\n";
    map(maudify($maudify,$_), "@lines" =~ /in\s+(.*?\.kmaude)/g);
    my $maude_file = ($kmaude_file =~ /^(.*)\.kmaude$/)[0].".maude";
    system "$maudify $kmaude_file > $maude_file";
}
