package Regexp::Common::balanced; {

use Regexp::Common qw /pattern clean no_defaults/;

use strict;
use warnings;

use vars qw /$VERSION/;
$VERSION = '2010010201';

my %closer = ( '{'=>'}', '('=>')', '['=>']', '<'=>'>' );
my $count = -1;
my %cache;

sub nested {
    my ($start, $finish) = @_;

    return $Regexp::Common::balanced [$cache {$start} {$finish}]
            if exists $cache {$start} {$finish};

    $count ++;
    my $r = '(??{$Regexp::Common::balanced ['. $count . ']})';

    my @starts   = map {s/\\(.)/$1/g; $_} grep {length}
                        $start  =~ /([^|\\]+|\\.)+/gs;
    my @finishes = map {s/\\(.)/$1/g; $_} grep {length}
                        $finish =~ /([^|\\]+|\\.)+/gs;

    push @finishes => ($finishes [-1]) x (@starts - @finishes);

    my @re;
    local $" = "|";
    foreach my $begin (@starts) {
        my $end = shift @finishes;

        my $qb  = quotemeta $begin;
        my $qe  = quotemeta $end;
        my $fb  = quotemeta substr $begin => 0, 1;
        my $fe  = quotemeta substr $end   => 0, 1;

        my $tb  = quotemeta substr $begin => 1;
        my $te  = quotemeta substr $end   => 1;

        use re 'eval';

        my $add;
        if ($fb eq $fe) {
            push @re =>
                   qr /(?:$qb(?:(?>[^$fb]+)|$fb(?!$tb)(?!$te)|$r)*$qe)/;
        }
        else {
            my   @clauses =  "(?>[^$fb$fe]+)";
            push @clauses => "$fb(?!$tb)" if length $tb;
            push @clauses => "$fe(?!$te)" if length $te;
            push @clauses =>  $r;
            push @re      =>  qr /(?:$qb(?:@clauses)*$qe)/;
        }
    }

    $cache {$start} {$finish} = $count;
    $Regexp::Common::balanced [$count] = qr/@re/;
}


pattern name    => [qw /balanced -parens=() -begin= -end=/],
        create  => sub {
            my $flag = $_[1];
            unless (defined $flag -> {-begin} && length $flag -> {-begin} &&
                    defined $flag -> {-end}   && length $flag -> {-end}) {
                my @open  = grep {index ($flag->{-parens}, $_) >= 0}
                             ('[','(','{','<');
                my @close = map {$closer {$_}} @open;
                $flag -> {-begin} = join "|" => @open;
                $flag -> {-end}   = join "|" => @close;
            }
            my $pat = nested @$flag {qw /-begin -end/};
            return exists $flag -> {-keep} ? qr /($pat)/ : $pat;
        },
        version => 5.006,
        ;

}

1;

__END__

=pod

=head1 NAME

Regexp::Common::balanced -- provide regexes for strings with balanced
parenthesized delimiters or arbitrary delimiters.

=head1 SYNOPSIS

    use Regexp::Common qw /balanced/;

    while (<>) {
        /$RE{balanced}{-parens=>'()'}/
                                   and print q{balanced parentheses\n};
    }


=head1 DESCRIPTION

Please consult the manual of L<Regexp::Common> for a general description
of the works of this interface.

Do not use this module directly, but load it via I<Regexp::Common>.

=head2 C<$RE{balanced}{-parens}>

Returns a pattern that matches a string that starts with the nominated
opening parenthesis or bracket, contains characters and properly nested
parenthesized subsequences, and ends in the matching parenthesis.

More than one type of parenthesis can be specified:

        $RE{balanced}{-parens=>'(){}'}

in which case all specified parenthesis types must be correctly balanced within
the string.

If we are using C{-keep} (See L<Regexp::Common>):

=over 4

=item $1

captures the entire expression

=back

=head2 C<< $RE{balanced}{-begin => "begin"}{-end => "end"} >>

Returns a pattern that matches a string that is properly balanced
using the I<begin> and I<end> strings as start and end delimiters.
Multiple sets of begin and end strings can be given by separating
them by C<|>s (which can be escaped with a backslash).

    qr/$RE{balanced}{-begin => "do|if|case"}{-end => "done|fi|esac"}/

will match properly balanced strings that either start with I<do> and
end with I<done>, start with I<if> and end with I<fi>, or start with
I<case> and end with I<esac>.

If I<-end> contains less cases than I<-begin>, the last case of I<-end>
is repeated. If it contains more cases than I<-begin>, the extra cases
are ignored. If either of I<-begin> or I<-end> isn't given, or is empty,
I<< -begin => '(' >> and I<< -end => ')' >> are assumed.

If we are using C{-keep} (See L<Regexp::Common>):

=over 4

=item $1

captures the entire expression

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
