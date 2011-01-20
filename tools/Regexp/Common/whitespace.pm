package Regexp::Common::whitespace;

use Regexp::Common qw /pattern clean no_defaults/;

use strict;
use warnings;

use vars qw /$VERSION/;
$VERSION = '2010010201';

pattern name   => [qw (ws crop)],
        create => '(?:^\s+|\s+$)',
        subs   => sub {$_[1] =~ s/^\s+//; $_[1] =~ s/\s+$//;}
        ;


1;

__END__

=pod

=head1 NAME

Regexp::Common::whitespace -- provides a regex for leading or
trailing whitescape

=head1 SYNOPSIS

    use Regexp::Common qw /whitespace/;

    while (<>) {
        s/$RE{ws}{crop}//g;           # Delete surrounding whitespace
    }


=head1 DESCRIPTION

Please consult the manual of L<Regexp::Common> for a general description
of the works of this interface.

Do not use this module directly, but load it via I<Regexp::Common>.


=head2 C<$RE{ws}{crop}>

Returns a pattern that identifies leading or trailing whitespace.

For example:

        $str =~ s/$RE{ws}{crop}//g;     # Delete surrounding whitespace

The call:

        $RE{ws}{crop}->subs($str);

is optimized (but probably still slower than doing the s///g explicitly).

This pattern does not capture under C<-keep>.

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
