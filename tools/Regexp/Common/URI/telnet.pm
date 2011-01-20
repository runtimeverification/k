package Regexp::Common::URI::telnet;

use Regexp::Common               qw /pattern clean no_defaults/;
use Regexp::Common::URI          qw /register_uri/;
use Regexp::Common::URI::RFC1738 qw /$user $password $host $port/;

use strict;
use warnings;

use vars qw /$VERSION/;
$VERSION = '2010010201';


my $telnet_uri = "(?k:(?k:telnet)://(?:(?k:(?k:$user)(?::(?k:$password))?)\@)?" 
               . "(?k:(?k:$host)(?::(?k:$port))?)(?k:/)?)";

register_uri telnet => $telnet_uri;

pattern name    => [qw (URI telnet)],
        create  => $telnet_uri,
        ;

1;

__END__

=pod

=head1 NAME

Regexp::Common::URI::telnet -- Returns a pattern for telnet URIs.

=head1 SYNOPSIS

    use Regexp::Common qw /URI/;

    while (<>) {
        /$RE{URI}{telnet}/       and  print "Contains a telnet URI.\n";
    }

=head1 DESCRIPTION

=head2 $RE{URI}{telnet}

Returns a pattern that matches I<telnet> URIs, as defined by RFC 1738.
Telnet URIs have the form:

    "telnet:" "//" [ user [ ":" password ] "@" ] host [ ":" port ] [ "/" ]

Under C<{-keep}>, the following are returned:

=over 4

=item $1

The complete URI.

=item $2

The scheme.

=item $3

The username:password combo, or just the username if there is no password.

=item $4

The username, if given.

=item $5

The password, if given.

=item $6

The host:port combo, or just the host if there's no port.

=item $7

The host.

=item $8

The port, if given.

=item $9

The trailing slash, if any.

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
