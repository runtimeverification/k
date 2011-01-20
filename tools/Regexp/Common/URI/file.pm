package Regexp::Common::URI::file;

use Regexp::Common               qw /pattern clean no_defaults/;
use Regexp::Common::URI          qw /register_uri/;
use Regexp::Common::URI::RFC1738 qw /$host $fpath/;

use strict;
use warnings;

use vars qw /$VERSION/;
$VERSION = '2010010201';


my $scheme = 'file';
my $uri    = "(?k:(?k:$scheme)://(?k:(?k:(?:$host|localhost)?)" .
             "(?k:/(?k:$fpath))))";

register_uri $scheme => $uri;

pattern name    => [qw (URI file)],
        create  => $uri,
        ;

1;

__END__

=pod

=head1 NAME

Regexp::Common::URI::file -- Returns a pattern for file URIs.

=head1 SYNOPSIS

    use Regexp::Common qw /URI/;

    while (<>) {
        /$RE{URI}{file}/       and  print "Contains a file URI.\n";
    }

=head1 DESCRIPTION

=head2 $RE{URI}{file}

Returns a pattern that matches I<file> URIs, as defined by RFC 1738.
File URIs have the form:

    "file:" "//" [ host | "localhost" ] "/" fpath

Under C<{-keep}>, the following are returned:

=over 4

=item $1

The complete URI.

=item $2

The scheme.

=item $3

The part of the URI following "file://".

=item $4

The hostname.

=item $5

The path name, including the leading slash.

=item $6

The path name, without the leading slash.

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

Damian Conway (damian@conway.org)

=head1 MAINTAINANCE

This package is maintained by Abigail S<(I<regexp-common@abigail.be>)>.

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
