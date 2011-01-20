package Regexp::Common::URI::pop;

use Regexp::Common               qw /pattern clean no_defaults/;
use Regexp::Common::URI          qw /register_uri/;
use Regexp::Common::URI::RFC1738 qw /$host $port/;
use Regexp::Common::URI::RFC2384 qw /$enc_user $enc_auth_type/;

use strict;
use warnings;

use vars qw /$VERSION/;
$VERSION = '2010010201';


my $scheme = "pop";
my $uri    = "(?k:(?k:$scheme)://(?:(?k:$enc_user)"     .  
             "(?:;AUTH=(?k:[*]|$enc_auth_type))?\@)?"   .
             "(?k:$host)(?::(?k:$port))?)";

register_uri $scheme => $uri;

pattern name    => [qw (URI POP)],
        create  => $uri,
        ;

1;

__END__

=pod

=head1 NAME

Regexp::Common::URI::pop -- Returns a pattern for POP URIs.

=head1 SYNOPSIS

    use Regexp::Common qw /URI/;

    while (<>) {
        /$RE{URI}{POP}/       and  print "Contains a POP URI.\n";
    }

=head1 DESCRIPTION

=head2 $RE{URI}{POP}

Returns a pattern that matches I<POP> URIs, as defined by RFC 2384.
POP URIs have the form:

    "pop:" "//" [ user [ ";AUTH" ( "*" | auth_type ) ] "@" ]
                  host [ ":" port ]

Under C<{-keep}>, the following are returned:

=over 4

=item $1

The complete URI.

=item $2

The I<scheme>.

=item $3

The I<user>, if given.

=item $4

The I<authentication type>, if given (could be a I<*>).

=item $5

The I<host>.

=item $6

The I<port>, if given.

=back

=head1 REFERENCES

=over 4

=item B<[RFC 2384]>

Gellens, R.: I<POP URL Scheme>. August 1998.

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
