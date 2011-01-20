package Regexp::Common::comment;

use Regexp::Common qw /pattern clean no_defaults/;

use strict;
use warnings;

use vars qw /$VERSION/;
$VERSION = '2010010201';

my @generic = (
    {languages => [qw /ABC Forth/],
     to_eol    => ['\\\\']},   # This is for just a *single* backslash.

    {languages => [qw /Ada Alan Eiffel lua/],
     to_eol    => ['--']},

    {languages => [qw /Advisor/],
     to_eol    => ['#|//']},

    {languages => [qw /Advsys CQL Lisp LOGO M MUMPS REBOL Scheme
                       SMITH zonefile/],
     to_eol    => [';']},

    {languages => ['Algol 60'],
     from_to   => [[qw /comment ;/]]},

    {languages => [qw {ALPACA B C C-- LPC PL/I}],
     from_to   => [[qw {/* */}]]},

    {languages => [qw /awk fvwm2 Icon m4 mutt Perl Python QML
                       R Ruby shell Tcl/],
     to_eol    => ['#']},

    {languages => [[BASIC => 'mvEnterprise']],
     to_eol    => ['[*!]|REM']},

    {languages => [qw /Befunge-98 Funge-98 Shelta/],
     id        => [';']},

    {languages => ['beta-Juliet', 'Crystal Report', 'Portia', 'Ubercode'],
     to_eol    => ['//']},

    {languages => ['BML'],
     from_to   => [['<?_c', '_c?>']],
    },

    {languages => [qw /C++/, 'C#', qw /Cg ECMAScript FPL Java JavaScript/],
     to_eol    => ['//'],
     from_to   => [[qw {/* */}]]},

    {languages => [qw /CLU LaTeX slrn TeX/],
     to_eol    => ['%']},

    {languages => [qw /False/],
     from_to   => [[qw !{ }!]]},

    {languages => [qw /Fortran/],
     to_eol    => ['!']},

    {languages => [qw /Haifu/],
     id        => [',']},

    {languages => [qw /ILLGOL/],
     to_eol    => ['NB']},

    {languages => [qw /INTERCAL/],
     to_eol    => [q{(?:(?:PLEASE(?:\s+DO)?|DO)\s+)?(?:NOT|N'T)}]},

    {languages => [qw /J/],
     to_eol    => ['NB[.]']},

    {languages => [qw /Nickle/],
     to_eol    => ['#'],
     from_to   => [[qw {/* */}]]},

    {languages => [qw /Oberon/],
     from_to   => [[qw /(* *)/]]},
     
    {languages => [[qw /Pascal Delphi/], [qw /Pascal Free/], [qw /Pascal GPC/]],
     to_eol    => ['//'],
     from_to   => [[qw !{ }!], [qw !(* *)!]]},

    {languages => [[qw /Pascal Workshop/]],
     id        => [qw /"/],
     from_to   => [[qw !{ }!], [qw !(* *)!], [qw !/* */!]]},

    {languages => [qw /PEARL/],
     to_eol    => ['!'],
     from_to   => [[qw {/* */}]]},

    {languages => [qw /PHP/],
     to_eol    => ['#', '//'],
     from_to   => [[qw {/* */}]]},

    {languages => [qw !PL/B!],
     to_eol    => ['[.;]']},

    {languages => [qw !PL/SQL!],
     to_eol    => ['--'],
     from_to   => [[qw {/* */}]]},

    {languages => [qw /Q-BAL/],
     to_eol    => ['`']},

    {languages => [qw /Smalltalk/],
     id        => ['"']},

    {languages => [qw /SQL/],
     to_eol    => ['-{2,}']},

    {languages => [qw /troff/],
     to_eol    => ['\\\"']},

    {languages => [qw /vi/],
     to_eol    => ['"']},

    {languages => [qw /*W/],
     from_to   => [[qw {|| !!}]]},

    {languages => [qw /ZZT-OOP/],
     to_eol    => ["'"]},
);

my @plain_or_nested = (
   [Caml         =>  undef,       "(*"  => "*)"],
   [Dylan        =>  "//",        "/*"  => "*/"],
   [Haskell      =>  "-{2,}",     "{-"  => "-}"],
   [Hugo         =>  "!(?!\\\\)", "!\\" => "\\!"],
   [SLIDE        =>  "#",         "(*"  => "*)"],
  ['Modula-2'    =>  undef,       "(*"  => "*)"],
  ['Modula-3'    =>  undef,       "(*"  => "*)"],
);

#
# Helper subs.
#

sub combine      {
    local $_ = join "|", @_;
    if (@_ > 1) {
        s/\(\?k:/(?:/g;
        $_ = "(?k:$_)";
    }
    $_
}

sub to_eol  ($)  {"(?k:(?k:$_[0])(?k:[^\\n]*)(?k:\\n))"}
sub id      ($)  {"(?k:(?k:$_[0])(?k:[^$_[0]]*)(?k:$_[0]))"}  # One char only!
sub from_to      {
    my ($begin, $end) = @_;

    my $qb  = quotemeta $begin;
    my $qe  = quotemeta $end;
    my $fe  = quotemeta substr $end   => 0, 1;
    my $te  = quotemeta substr $end   => 1;

    "(?k:(?k:$qb)(?k:(?:[^$fe]+|$fe(?!$te))*)(?k:$qe))";
}


my $count = 0;
sub nested {
    my ($begin, $end) = @_;

    $count ++;
    my $r = '(??{$Regexp::Common::comment ['. $count . ']})';

    my $qb  = quotemeta $begin;
    my $qe  = quotemeta $end;
    my $fb  = quotemeta substr $begin => 0, 1;
    my $fe  = quotemeta substr $end   => 0, 1;

    my $tb  = quotemeta substr $begin => 1;
    my $te  = quotemeta substr $end   => 1;

    use re 'eval';

    my $re;
    if ($fb eq $fe) {
        $re = qr /(?:$qb(?:(?>[^$fb]+)|$fb(?!$tb)(?!$te)|$r)*$qe)/;
    }
    else {
        local $"      =  "|";
        my   @clauses =  "(?>[^$fb$fe]+)";
        push @clauses => "$fb(?!$tb)" if length $tb;
        push @clauses => "$fe(?!$te)" if length $te;
        push @clauses =>  $r;
        $re           =   qr /(?:$qb(?:@clauses)*$qe)/;
    }

    $Regexp::Common::comment [$count] = qr/$re/;
}

#
# Process data.
#

foreach my $info (@plain_or_nested) {
    my ($language, $mark, $begin, $end) = @$info;
    pattern name    => [comment => $language],
            create  =>
                sub {my $re     = nested $begin => $end;
                     my $prefix = defined $mark ? $mark . "[^\n]*\n|" : "";
                     exists $_ [1] -> {-keep} ? qr /($prefix$re)/
                                              : qr  /$prefix$re/
                },
            version => 5.006,
            ;
}


foreach my $group (@generic) {
    my $pattern = combine +(map {to_eol   $_} @{$group -> {to_eol}}),
                           (map {from_to @$_} @{$group -> {from_to}}),
                           (map {id       $_} @{$group -> {id}}),
                  ;
    foreach my $language  (@{$group -> {languages}}) {
        pattern name    => [comment => ref $language ? @$language : $language],
                create  => $pattern,
                ;
    }
}
                

    
#
# Other languages.
#

# http://www.pascal-central.com/docs/iso10206.txt
pattern name    => [qw /comment Pascal/],
        create  => '(?k:' . '(?k:[{]|[(][*])'
                          . '(?k:[^}*]*(?:[*](?![)])[^}*]*)*)'
                          . '(?k:[}]|[*][)])'
                          . ')'
        ;

# http://www.templetons.com/brad/alice/language/
pattern name    =>  [qw /comment Pascal Alice/],
        create  =>  '(?k:(?k:[{])(?k:[^}\n]*)(?k:[}]))'
        ;


# http://westein.arb-phys.uni-dortmund.de/~wb/a68s.txt
pattern name    => [qw (comment), 'Algol 68'],
        create  => q {(?k:(?:#[^#]*#)|}                           .
                   q {(?:\bco\b(?:[^c]+|\Bc|\bc(?!o\b))*\bco\b)|} .
                   q {(?:\bcomment\b(?:[^c]+|\Bc|\bc(?!omment\b))*\bcomment\b))}
        ;


# See rules 91 and 92 of ISO 8879 (SGML).
# Charles F. Goldfarb: "The SGML Handbook".
# Oxford: Oxford University Press. 1990. ISBN 0-19-853737-9.
# Ch. 10.3, pp 390.
pattern name    => [qw (comment HTML)],
        create  => q {(?k:(?k:<!)(?k:(?:--(?k:[^-]*(?:-[^-]+)*)--\s*)*)(?k:>))},
        ;


pattern name    => [qw /comment SQL MySQL/],
        create  => q {(?k:(?:#|-- )[^\n]*\n|} .
                   q {/\*(?:(?>[^*;"']+)|"[^"]*"|'[^']*'|\*(?!/))*(?:;|\*/))},
        ;

# Anything that isn't <>[]+-.,
# http://home.wxs.nl/~faase009/Ha_BF.html
pattern name    => [qw /comment Brainfuck/],
        create  => '(?k:[^<>\[\]+\-.,]+)'
        ;

# Squeak is a variant of Smalltalk-80.
# http://www.squeak.
# http://mucow.com/squeak-qref.html
pattern name    => [qw /comment Squeak/],
        create  => '(?k:(?k:")(?k:[^"]*(?:""[^"]*)*)(?k:"))'
        ;

#
# Scores of less than 5 or above 17....
# http://www.cliff.biffle.org/esoterica/beatnik.html
@Regexp::Common::comment::scores = (1,  3,  3,  2,  1,  4,  2,  4,  1,  8,
                                    5,  1,  3,  1,  1,  3, 10,  1,  1,  1,
                                    1,  4,  4,  8,  4, 10);
{
my ($s, $x);
pattern name    =>  [qw /comment Beatnik/],
        create  =>  sub {
            use re 'eval';
            my $re = qr {\b([A-Za-z]+)\b
                         (?(?{($s, $x) = (0, lc $^N);
                              $s += $Regexp::Common::comment::scores
                                    [ord (chop $x) - ord ('a')] while length $x;
                              $s  >= 5 && $s < 18})XXX|)}x;
            $re;
        },
        version  => 5.008,
        ;
}


# http://www.cray.com/craydoc/manuals/007-3692-005/html-007-3692-005/
#  (Goto table of contents/3.3 Source Form)
# Fortran, in fixed format. Comments start with a C, c or * in the first
# column, or a ! anywhere, but the sixth column. Then end with a newline.
pattern name    =>  [qw /comment Fortran fixed/],
        create  =>  '(?k:(?k:(?:^[Cc*]|(?<!^.....)!))(?k:[^\n]*)(?k:\n))'
        ;


# http://www.csis.ul.ie/cobol/Course/COBOLIntro.htm
# Traditionally, comments in COBOL were indicated with an asteriks in
# the seventh column. Modern compilers may be more lenient.
pattern name    =>  [qw /comment COBOL/],
        create  =>  '(?<=^......)(?k:(?k:[*])(?k:[^\n]*)(?k:\n))',
        version =>  '5.008',
        ;

1;


__END__

=pod

=head1 NAME

Regexp::Common::comment -- provide regexes for comments.

=head1 SYNOPSIS

    use Regexp::Common qw /comment/;

    while (<>) {
        /$RE{comment}{C}/       and  print "Contains a C comment\n";
        /$RE{comment}{C++}/     and  print "Contains a C++ comment\n";
        /$RE{comment}{PHP}/     and  print "Contains a PHP comment\n";
        /$RE{comment}{Java}/    and  print "Contains a Java comment\n";
        /$RE{comment}{Perl}/    and  print "Contains a Perl comment\n";
        /$RE{comment}{awk}/     and  print "Contains an awk comment\n";
        /$RE{comment}{HTML}/    and  print "Contains an HTML comment\n";
    }

    use Regexp::Common qw /comment RE_comment_HTML/;

    while (<>) {
        $_ =~ RE_comment_HTML() and  print "Contains an HTML comment\n";
    }

=head1 DESCRIPTION

Please consult the manual of L<Regexp::Common> for a general description
of the works of this interface.

Do not use this module directly, but load it via I<Regexp::Common>.

This modules gives you regular expressions for comments in various
languages.

=head2 THE LANGUAGES

Below, the comments of each of the languages are described.
The patterns are available as C<$RE{comment}{I<LANG>}>, foreach
language I<LANG>. Some languages have variants; it's described
at the individual languages how to get the patterns for the variants.
Unless mentioned otherwise,
C<{-keep}> sets C<$1>, C<$2>, C<$3> and C<$4> to the entire comment,
the opening marker, the content of the comment, and the closing marker
(for many languages, the latter is a newline) respectively.

=over 4

=item ABC

Comments in I<ABC> start with a backslash (C<\>), and last till
the end of the line.
See L<http://homepages.cwi.nl/%7Esteven/abc/>.

=item Ada

Comments in I<Ada> start with C<-->, and last till the end of the line.

=item Advisor

I<Advisor> is a language used by the HP product I<glance>. Comments for
this language start with either C<#> or C<//>, and last till the
end of the line.

=item Advsys

Comments for the I<Advsys> language start with C<;> and last till
the end of the line. See also L<http://www.wurb.com/if/devsys/12>.

=item Alan

I<Alan> comments start with C<-->, and last till the end of the line.
See also L<http://w1.132.telia.com/~u13207378/alan/manual/alanTOC.html>.

=item Algol 60

Comments in the I<Algol 60> language start with the keyword C<comment>,
and end with a C<;>. See L<http://www.masswerk.at/algol60/report.htm>.

=item Algol 68

In I<Algol 68>, comments are either delimited by C<#>, or by one of the
keywords C<co> or C<comment>. The keywords should not be part of another
word. See L<http://westein.arb-phys.uni-dortmund.de/~wb/a68s.txt>.
With C<{-keep}>, only C<$1> will be set, returning the entire comment.

=item ALPACA

The I<ALPACA> language has comments starting with C</*> and ending with C<*/>.

=item awk

The I<awk> programming language uses comments that start with C<#>
and end at the end of the line.

=item B

The I<B> language has comments starting with C</*> and ending with C<*/>.

=item BASIC

There are various forms of BASIC around. Currently, we only support the
variant supported by I<mvEnterprise>, whose pattern is available as
C<$RE{comment}{BASIC}{mvEnterprise}>. Comments in this language start with a
C<!>, a C<*> or the keyword C<REM>, and end till the end of the line. See
L<http://www.rainingdata.com/products/beta/docs/mve/50/ReferenceManual/Basic.pdf>.

=item Beatnik

The esotoric language I<Beatnik> only uses words consisting of letters.
Words are scored according to the rules of Scrabble. Words scoring less
than 5 points, or 18 points or more are considered comments (although
the compiler might mock at you if you score less than 5 points).
Regardless whether C<{-keep}>, C<$1> will be set, and set to the
entire comment. This pattern requires I<perl 5.8.0> or newer.

=item beta-Juliet

The I<beta-Juliet> programming language has comments that start with
C<//> and that continue till the end of the line. See also
L<http://www.catseye.mb.ca/esoteric/b-juliet/index.html>.

=item Befunge-98

The esotoric language I<Befunge-98> uses comments that start and end
with a C<;>. See L<http://www.catseye.mb.ca/esoteric/befunge/98/spec98.html>.

=item BML                 

I<BML>, or I<Better Markup Language> is an HTML templating language that
uses comments starting with C<< <?c_ >>, and ending with C<< c_?> >>.
See L<http://www.livejournal.com/doc/server/bml.index.html>.               

=item Brainfuck

The minimal language I<Brainfuck> uses only eight characters, 
C<E<lt>>, C<E<gt>>, C<[>, C<]>, C<+>, C<->, C<.> and C<,>.
Any other characters are considered comments. With C<{-keep}>,
C<$1> is set to the entire comment.

=item C

The I<C> language has comments starting with C</*> and ending with C<*/>.

=item C--

The I<C--> language has comments starting with C</*> and ending with C<*/>.
See L<http://cs.uas.arizona.edu/classes/453/programs/C--Spec.html>.

=item C++

The I<C++> language has two forms of comments. Comments that start with
C<//> and last till the end of the line, and comments that start with
C</*>, and end with C<*/>. If C<{-keep}> is used, only C<$1> will be
set, and set to the entire comment.

=item C#

The I<C#> language has two forms of comments. Comments that start with
C<//> and last till the end of the line, and comments that start with
C</*>, and end with C<*/>. If C<{-keep}> is used, only C<$1> will be
set, and set to the entire comment.
See L<http://msdn.microsoft.com/library/default.asp?url=/library/en-us/csspec/html/vclrfcsharpspec_C.asp>.

=item Caml

Comments in I<Caml> start with C<(*>, end with C<*)>, and can be nested.
See L<http://www.cs.caltech.edu/courses/cs134/cs134b/book.pdf> and
L<http://pauillac.inria.fr/caml/index-eng.html>.

=item Cg

The I<Cg> language has two forms of comments. Comments that start with
C<//> and last till the end of the line, and comments that start with
C</*>, and end with C<*/>. If C<{-keep}> is used, only C<$1> will be
set, and set to the entire comment.
See L<http://developer.nvidia.com/attach/3722>.

=item CLU

In C<CLU>, a comment starts with a procent sign (C<%>), and ends with the
next newline. See L<ftp://ftp.lcs.mit.edu:/pub/pclu/CLU-syntax.ps> and
L<http://www.pmg.lcs.mit.edu/CLU.html>.

=item COBOL

Traditionally, comments in I<COBOL> are indicated by an asteriks in the
seventh column. This is what the pattern matches. Modern compiler may
more lenient though. See L<http://www.csis.ul.ie/cobol/Course/COBOLIntro.htm>,
and L<http://www.csis.ul.ie/cobol/default.htm>. Due to a bug in the regexp
engine of perl 5.6.x, this regexp is only available in version 5.8.0 and up.

=item CQL

Comments in the chess query language (I<CQL>) start with a semi colon
(C<;>) and last till the end of the line. See L<http://www.rbnn.com/cql/>.

=item Crystal Report

The formula editor in I<Crystal Reports> uses comments that start
with C<//>, and end with the end of the line.

=item Dylan

There are two types of comments in I<Dylan>. They either start with
C<//>, or are nested comments, delimited with C</*> and C<*/>.
Under C<{-keep}>, only C<$1> will be set, returning the entire comment.
This pattern requires I<perl 5.6.0> or newer.

=item ECMAScript

The I<ECMAScript> language has two forms of comments. Comments that start with
C<//> and last till the end of the line, and comments that start with
C</*>, and end with C<*/>. If C<{-keep}> is used, only C<$1> will be
set, and set to the entire comment. I<JavaScript> is Netscapes implementation
of I<ECMAScript>. See
L<http://www.ecma-international.org/publications/files/ecma-st/Ecma-262.pdf>,
and L<http://www.ecma-international.org/publications/standards/Ecma-262.htm>.

=item Eiffel

I<Eiffel> comments start with C<-->, and last till the end of the line.

=item False

In I<False>, comments start with C<{> and end with C<}>.
See L<http://wouter.fov120.com/false/false.txt>

=item FPL

The I<FPL> language has two forms of comments. Comments that start with
C<//> and last till the end of the line, and comments that start with
C</*>, and end with C<*/>. If C<{-keep}> is used, only C<$1> will be
set, and set to the entire comment.

=item Forth

Comments in Forth start with C<\>, and end with the end of the line.
See also L<http://docs.sun.com/sb/doc/806-1377-10>.

=item Fortran

There are two forms of I<Fortran>. There's free form I<Fortran>, which
has comments that start with C<!>, and end at the end of the line.
The pattern for this is given by C<$RE{Fortran}>. Fixed form I<Fortran>,
which has been obsoleted, has comments that start with C<C>, C<c> or
C<*> in the first column, or with C<!> anywhere, but the sixth column.
The pattern for this are given by C<$RE{Fortran}{fixed}>.

See also L<http://www.cray.com/craydoc/manuals/007-3692-005/html-007-3692-005/>.

=item Funge-98

The esotoric language I<Funge-98> uses comments that start and end with
a C<;>.

=item fvwm2

Configuration files for I<fvwm2> have comments starting with a
C<#> and lasting the rest of the line.

=item Haifu

I<Haifu>, an esotoric language using haikus, has comments starting and
ending with a C<,>.
See L<http://www.dangermouse.net/esoteric/haifu.html>.

=item Haskell

There are two types of comments in I<Haskell>. They either start with
at least two dashes, or are nested comments, delimited with C<{-> and C<-}>.
Under C<{-keep}>, only C<$1> will be set, returning the entire comment.
This pattern requires I<perl 5.6.0> or newer.

=item HTML

In I<HTML>, comments only appear inside a I<comment declaration>.
A comment declaration starts with a C<E<lt>!>, and ends with a
C<E<gt>>. Inside this declaration, we have zero or more comments.
Comments starts with C<--> and end with C<-->, and are optionally
followed by whitespace. The pattern C<$RE{comment}{HTML}> recognizes
those comment declarations (and hence more than a comment).
Note that this is not the same as something that starts with
C<E<lt>!--> and ends with C<--E<gt>>, because the following will
be matched completely:

    <!--  First  Comment   --
      --> Second Comment <!--
      --  Third  Comment   -->

Do not be fooled by what your favourite browser thinks is an HTML
comment.

If C<{-keep}> is used, the following are returned:

=over 4

=item $1

captures the entire comment declaration.

=item $2

captures the MDO (markup declaration open), C<E<lt>!>.

=item $3

captures the content between the MDO and the MDC.

=item $4

captures the (last) comment, without the surrounding dashes.

=item $5

captures the MDC (markup declaration close), C<E<gt>>.

=back

=item Hugo

There are two types of comments in I<Hugo>. They either start with
C<!> (which cannot be followed by a C<\>), or are nested comments,
delimited with C<!\> and C<\!>.
Under C<{-keep}>, only C<$1> will be set, returning the entire comment.
This pattern requires I<perl 5.6.0> or newer.

=item Icon

I<Icon> has comments that start with C<#> and end at the next new line.
See L<http://www.toolsofcomputing.com/IconHandbook/IconHandbook.pdf>,
L<http://www.cs.arizona.edu/icon/index.htm>, and
L<http://burks.bton.ac.uk/burks/language/icon/index.htm>.

=item ILLGOL

The esotoric language I<ILLGOL> uses comments starting with I<NB> and lasting
till the end of the line.
See L<http://www.catseye.mb.ca/esoteric/illgol/index.html>.

=item INTERCAL

Comments in INTERCAL are single line comments. They start with one of
the keywords C<NOT> or C<N'T>, and can optionally be preceeded by the
keywords C<DO> and C<PLEASE>. If both keywords are used, C<PLEASE>
preceeds C<DO>. Keywords are separated by whitespace.

=item J

The language I<J> uses comments that start with C<NB.>, and that last till
the end of the line. See
L<http://www.jsoftware.com/books/help/primer/contents.htm>, and
L<http://www.jsoftware.com/>.

=item Java

The I<Java> language has two forms of comments. Comments that start with
C<//> and last till the end of the line, and comments that start with
C</*>, and end with C<*/>. If C<{-keep}> is used, only C<$1> will be
set, and set to the entire comment.

=item JavaScript

The I<JavaScript> language has two forms of comments. Comments that start with
C<//> and last till the end of the line, and comments that start with
C</*>, and end with C<*/>. If C<{-keep}> is used, only C<$1> will be
set, and set to the entire comment. I<JavaScript> is Netscapes implementation
of I<ECMAScript>.
See L<http://www.mozilla.org/js/language/E262-3.pdf>,
and L<http://www.mozilla.org/js/language/>.

=item LaTeX

The documentation language I<LaTeX> uses comments starting with C<%>
and ending at the end of the line.

=item Lisp

Comments in I<Lisp> start with a semi-colon (C<;>) and last till the
end of the line.

=item LPC

The I<LPC> language has comments starting with C</*> and ending with C<*/>.

=item LOGO

Comments for the language I<LOGO> start with C<;>, and last till the end
of the line.

=item lua

Comments for the I<lua> language start with C<-->, and last till the end
of the line. See also L<http://www.lua.org/manual/manual.html>.

=item M, MUMPS

In C<M> (aka C<MUMPS>), comments start with a semi-colon, and last
till the end of a line. The language specification requires the 
semi-colon to be preceeded by one or more I<linestart character>s.
Those characters default to a space, but that's configurable. This
requirement, of preceeding the comment with linestart characters is
B<not> tested for. See
L<ftp://ftp.intersys.com/pub/openm/ism/ism64docs.zip>,
L<http://mtechnology.intersys.com/mproducts/openm/index.html>, and
L<http://mcenter.com/mtrc/index.html>.

=item m4

By default, the preprocessor language I<m4> uses single line comments,
that start with a C<#> and continue to the end of the line, including
the newline. The pattern C<$RE {comment} {m4}> matches such comments.
In I<m4>, it is possible to change the starting token though.
See L<http://wolfram.schneider.org/bsd/7thEdManVol2/m4/m4.pdf>,
L<http://www.cs.stir.ac.uk/~kjt/research/pdf/expl-m4.pdf>, and
L<http://www.gnu.org/software/m4/manual/>.

=item Modula-2

In C<Modula-2>, comments start with C<(*>, and end with C<*)>. Comments
may be nested. See L<http://www.modula2.org/>.

=item Modula-3

In C<Modula-3>, comments start with C<(*>, and end with C<*)>. Comments
may be nested. See L<http://www.m3.org/>.

=item mutt

Configuration files for I<mutt> have comments starting with a
C<#> and lasting the rest of the line.

=item Nickle

The I<Nickle> language has one line comments starting with C<#>
(like Perl), or multiline comments delimited by C</*> and C<*/>
(like C). Under C<-keep>, only C<$1> will be set. See also
L<http://www.nickle.org>.

=item Oberon

Comments in I<Oberon> start with C<(*> and end with C<*)>.
See L<http://www.oberon.ethz.ch/oreport.html>.

=item Pascal

There are many implementations of Pascal. This modules provides
pattern for comments of several implementations.

=over 4

=item C<$RE{comment}{Pascal}>

This is the pattern that recognizes comments according to the Pascal ISO 
standard. This standard says that comments start with either C<{>, or
C<(*>, and end with C<}> or C<*)>. This means that C<{*)> and C<(*}>
are considered to be comments. Many Pascal applications don't allow this.
See L<http://www.pascal-central.com/docs/iso10206.txt>

=item C<$RE{comment}{Alice}>

The I<Alice Pascal> compiler accepts comments that start with C<{>
and end with C<}>. Comments are not allowed to contain newlines.
See L<http://www.templetons.com/brad/alice/language/>.

=item C<$RE{comment}{Pascal}{Delphi}>, C<$RE{comment}{Pascal}{Free}>
and C<$RE{comment}{Pascal}{GPC}>

The I<Delphi Pascal>, I<Free Pascal> and the I<Gnu Pascal Compiler>
implementations of Pascal all have comments that either start with
C<//> and last till the end of the line, are delimited with C<{>
and C<}> or are delimited with C<(*> and C<*)>. Patterns for those
comments are given by C<$RE{comment}{Pascal}{Delphi}>, 
C<$RE{comment}{Pascal}{Free}> and C<$RE{comment}{Pascal}{GPC}>
respectively. These patterns only set C<$1> when C<{-keep}> is used,
which will then include the entire comment.

See L<http://info.borland.com/techpubs/delphi5/oplg/>, 
L<http://www.freepascal.org/docs-html/ref/ref.html> and
L<http://www.gnu-pascal.de/gpc/>.

=item C<$RE{comment}{Pascal}{Workshop}>

The I<Workshop Pascal> compiler, from SUN Microsystems, allows comments
that are delimited with either C<{> and C<}>, delimited with
C<(*)> and C<*>), delimited with C</*>, and C<*/>, or starting
and ending with a double quote (C<">). When C<{-keep}> is used,
only C<$1> is set, and returns the entire comment.

See L<http://docs.sun.com/db/doc/802-5762>.

=back

=item PEARL

Comments in I<PEARL> start with a C<!> and last till the end of the
line, or start with C</*> and end with C<*/>. With C<{-keep}>, 
C<$1> will be set to the entire comment.

=item PHP

Comments in I<PHP> start with either C<#> or C<//> and last till the
end of the line, or are delimited by C</*> and C<*/>. With C<{-keep}>,
C<$1> will be set to the entire comment.

=item PL/B

In I<PL/B>, comments start with either C<.> or C<;>, and end with the 
next newline. See L<http://www.mmcctech.com/pl-b/plb-0010.htm>.

=item PL/I

The I<PL/I> language has comments starting with C</*> and ending with C<*/>.

=item PL/SQL

In I<PL/SQL>, comments either start with C<--> and run till the end
of the line, or start with C</*> and end with C<*/>.

=item Perl

I<Perl> uses comments that start with a C<#>, and continue till the end
of the line.

=item Portia

The I<Portia> programming language has comments that start with C<//>,
and last till the end of the line.

=item Python

I<Python> uses comments that start with a C<#>, and continue till the end
of the line.

=item Q-BAL

Comments in the I<Q-BAL> language start with C<`> (a backtick), and
contine till the end of the line.

=item QML

In C<QML>, comments start with C<#> and last till the end of the line.
See L<http://www.questionmark.com/uk/qml/overview.doc>.

=item R

The statistical language I<R> uses comments that start with a C<#> and
end with the following new line. See L<http://www.r-project.org/>.

=item REBOL

Comments for the I<REBOL> language start with C<;> and last till the
end of the line.

=item Ruby

Comments in I<Ruby> start with C<#> and last till the end of the time.

=item Scheme

I<Scheme> comments start with C<;>, and last till the end of the line.
See L<http://schemers.org/>.

=item shell

Comments in various I<shell>s start with a C<#> and end at the end of
the line.

=item Shelta

The esotoric language I<Shelta> uses comments that start and end with
a C<;>. See L<http://www.catseye.mb.ca/esoteric/shelta/index.html>.

=item SLIDE

The I<SLIDE> language has two froms of comments. First there is the
line comment, which starts with a C<#> and includes the rest of the
line (just like Perl). Second, there is the multiline, nested comment,
which are delimited by C<(*> and C<*)>. Under C{-keep}>, only 
C<$1> is set, and is set to the entire comment. This pattern needs
at least Perl version 5.6.0. See
L<http://www.cs.berkeley.edu/~ug/slide/docs/slide/spec/spec_frame_intro.shtml>.

=item slrn

Configuration files for I<slrn> have comments starting with a
C<%> and lasting the rest of the line.

=item Smalltalk

I<Smalltalk> uses comments that start and end with a double quote, C<">.

=item SMITH

Comments in the I<SMITH> language start with C<;>, and last till the
end of the line.

=item Squeak

In the Smalltalk variant I<Squeak>, comments start and end with
C<">. Double quotes can appear inside comments by doubling them.

=item SQL

Standard I<SQL> uses comments starting with two or more dashes, and
ending at the end of the line. 

I<MySQL> does not follow the standard. Instead, it allows comments
that start with a C<#> or C<-- > (that's two dashes and a space)
ending with the following newline, and comments starting with 
C</*>, and ending with the next C<;> or C<*/> that isn't inside
single or double quotes. A pattern for this is returned by
C<$RE{comment}{SQL}{MySQL}>. With C<{-keep}>, only C<$1> will
be set, and it returns the entire comment.

=item Tcl

In I<Tcl>, comments start with C<#> and continue till the end of the line.

=item TeX

The documentation language I<TeX> uses comments starting with C<%>
and ending at the end of the line.

=item troff

The document formatting language I<troff> uses comments starting
with C<\">, and continuing till the end of the line.

=item Ubercode

The Windows programming language I<Ubercode> uses comments that start with
C<//> and continue to the end of the line. See L<http://www.ubercode.com>.

=item vi

In configuration files for the editor I<vi>, one can use comments
starting with C<">, and ending at the end of the line.

=item *W

In the language I<*W>, comments start with C<||>, and end with C<!!>.

=item zonefile

Comments in DNS I<zonefile>s start with C<;>, and continue till the
end of the line.

=item ZZT-OOP

The in-game language I<ZZT-OOP> uses comments that start with a C<'> 
character, and end at the following newline. See
L<http://dave2.rocketjump.org/rad/zzthelp/lang.html>.

=back

=head1 REFERENCES

=over 4

=item B<[Go 90]>

Charles F. Goldfarb: I<The SGML Handbook>. Oxford: Oxford University
Press. B<1990>. ISBN 0-19-853737-9. Ch. 10.3, pp 390-391.

=back

=head1 SEE ALSO

L<Regexp::Common> for a general description of how to use this interface.

=head1 AUTHOR

Damian Conway (damian@conway.org)

=head1 MAINTAINANCE

This package is maintained by Abigail S<(I<regexp-common@abigail.be>)>.

=head1 BUGS AND IRRITATIONS

Bound to be plenty.

For a start, there are many common regexes missing.
Send them in to I<regexp-common@abigail.be>.

=head1 LICENSE and COPYRIGHT

This software is Copyright (c) 2001 - 2009, Damian Conway and Abigail.

This module is free software, and maybe used under any of the following
licenses:

 1) The Perl Artistic License.     See the file COPYRIGHT.AL.
 2) The Perl Artistic License 2.0. See the file COPYRIGHT.AL2.
 3) The BSD Licence.               See the file COPYRIGHT.BSD.
 4) The MIT Licence.               See the file COPYRIGHT.MIT.

=cut
