package Regexp::Common::URI::prospero;

use Regexp::Common               qw /pattern clean no_defaults/;
use Regexp::Common::URI          qw /register_uri/;
use Regexp::Common::URI::RFC1738 qw /$host $port $ppath $fieldname $fieldvalue
                                     $fieldspec/;

use strict;
use warnings;

use vars qw /$VERSION/;
$VERSION = '2010010201';


my $scheme = 'prospero';
my $uri    = "(?k:(?k:$scheme)://(?k:$host)(?::(?k:$port))?" .
             "/(?k:$ppath)(?k:$fieldspec*))";

register_uri $scheme => $uri;

pattern name    => [qw (URI prospero)],
        create  => $uri,
        ;

1;

__END__

=pod

=head1 NAME

Regexp::Common::URI::prospero -- Returns a pattern for prospero URIs.

=head1 SYNOPSIS

    use Regexp::Common qw /URI/;

    while (<>) {
        /$RE{URI}{prospero}/ and print "Contains a prospero URI.\n";
    }

=head1 DESCRIPTION

=head2 $RE{URI}{prospero}

Returns a pattern that matches I<prospero> URIs, as defined by RFC 1738.
prospero URIs have the form:

    "prospero:" "//" host [ ":" port ] "/" path [ fieldspec ] *

Under C<{-keep}>, the following are returned:

=over 4

=item $1

The complete URI.

=item $2

The I<scheme>.

=item $3

The I<hostname>.

=item $4

The I<port>, if given.

=item $5

The propero path.

=item $6

The field specifications, if given. There can be more field specifications;
they will all be returned in C<$6>.

=back

=head1 REFERENCES

=over 4

=item B<[RFC 1738]>

Berners-Lee, Tim, Masinter, L., McCahill, M.: I<Uniform Resource
Locators (URL)>. December 1994.

=back

=head1 SEE ALSO

L<Regexp::Common::URI> for other supported URIs.

=head1 AUTHOR

Abigail. (I<regexp-common@abigail.be>).

=head1 BUGS AND IRRITATIONS

Bound to be plenty.

=head1 LICENSE and COPYRIGHT

This software is Copyright (c) 2001 - 2009, Damian Conway and Abigail.

This module is free software, and maybe used under any of the following
licenses:

 1) The Perl Artistic License.     See the file COPYRIGHT.AL.
 2) The Perl Artistic License 2.0. See the file COPYRIGHT.AL2.
 3) The BSD Licence.               See the file COPYRIGHT.BSD.
 4) The MIT Licence.               See the file COPYRIGHT.MIT.

=cut
