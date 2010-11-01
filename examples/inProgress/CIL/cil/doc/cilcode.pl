#
# Preprocesses a text and it changes
# \begin{cilcode}
# ...
# \end{cilcode}
#
# into the verbatim environment and add the option to see the CIL output for
# it.

use strict;
use Data::Dumper;

my $testnr = 1;
my $tmpdir  = "cilcode.tmp";
my $htmloutdir = "examples";
my $outdir  = "html/cil/$htmloutdir";

my $cilly = "perl ../bin/cilly --verbose";

my $doexamples = ! defined($ENV{'NO_EXAMPLES'});

my $preambleLocal = <<EOF;
int main(void) {
\# 1
EOF

my $preambleGlobal = <<EOF;
EOF

my $postambleGlobal = "";
my $postambleLocal = <<EOF;
}
EOF

if(! -d $tmpdir) {
    mkdir $tmpdir || die "Canmake not make $tmpdir\n";

}
my $incode = 0;
my $opt;
my $cil_options;

binmode STDOUT;

my $lineno = 0;
while(<>) {
    $lineno ++;
    if(! $incode && $_ =~ m|^\\begin{cilcode}\[(.*)\](.*)$|) {
        $opt = $1;
        $cil_options = $2;
        $incode = 1;
        print STDERR "\n***Found CIL code at line $lineno\n";
        open(TSTSRC, ">$tmpdir/ex$testnr.c") 
            || die "Cannot create source $testnr";
        if($opt eq 'local') {
            print TSTSRC $preambleLocal;
        } else {
            print TSTSRC $preambleGlobal;
        }
        print "\\begin{code}\n";
        next;
    }
    if($incode && $_ =~ m|^\\end{cilcode}$|) {
        $incode = 0;
        if($opt eq 'local') {
            print TSTSRC $postambleLocal;
        } else {
            print TSTSRC $postambleGlobal;
        }
        close(TSTSRC);
        print "\\end{verbatim}\\end{code}\n";
        if($doexamples) {
            print "See the \\ahref{$htmloutdir/ex$testnr.txt}{CIL output} for this
code fragment\n";
            # Now run cilly
            my $cmd = "$cilly $cil_options -c $tmpdir/ex$testnr.c -o $tmpdir/ex$testnr.o --save-temps=$tmpdir";
            # print "$cmd\n";
            if(system($cmd)) {
                die "Error running CIL for $tmpdir/ex$testnr.c";
            }
            # Now repackage the CIL file
            my $cilfile = "$tmpdir/ex$testnr.cil.c";
            open(CIL, "<$cilfile") || die "Cannot find CIL file \"$cilfile\" for $testnr";
            my $exfile = "$outdir/ex$testnr.txt";
            open(OUT, ">$exfile") || die "Cannot write OUT file \"$exfile\" for $testnr";
            while(<CIL>) {
                print OUT $_;
            }
            close(OUT);
            close(CIL);
        } else {
            print "(Code generation was turned off for this document)";
        }
        $testnr ++;
        next;
    }
    if($incode) {
        print TSTSRC $_;
    } 
    print $_;
}

