package Regexp::Common::URI::tel;

use Regexp::Common               qw /pattern clean no_defaults/;
use Regexp::Common::URI          qw /register_uri/;
use Regexp::Common::URI::RFC2806 qw /$telephone_subscriber 
                                     $telephone_subscriber_no_future/;

use strict;
use warnings;

use vars qw /$VERSION/;
$VERSION = '2010010201';


my $tel_scheme  = 'tel';
my $tel_uri     = "(?k:(?k:$tel_scheme):(?k:$telephone_subscriber))";
my $tel_uri_nf  = "(?k:(?k:$tel_scheme):(?k:$telephone_subscriber_no_future))";

register_uri $tel_scheme => $tel_uri;

pattern name    => [qw (URI tel)],
        create  => $tel_uri
        ;

pattern name    => [qw (URI tel nofuture)],
        create  => $tel_uri_nf
        ;

1;

__END__

=pod

=head1 NAME

Regexp::Common::URI::tel -- Returns a pattern for telephone URIs.

=head1 SYNOPSIS

    use Regexp::Common qw /URI/;

    while (<>) {
        /$RE{URI}{tel}/       and  print "Contains a telephone URI.\n";
    }

=head1 DESCRIPTION

=head2 $RE{URI}{tel}

Returns a pattern that matches I<tel> URIs, as defined by RFC 2806.
Under C<{-keep}>, the following are returned:

=over 4

=item $1

The complete URI.

=item $2

The scheme.

=item $3

The phone number, including any possible add-ons like ISDN subaddress,
a post dial part, area specifier, service provider, etc.

=back

=head2 C<$RE{URI}{tel}{nofuture}>

As above (including what's returned by C<{-keep}>), with the exception
that I<future extensions> are not allowed. Without allowing 
those I<future extensions>, it becomes much easier to check a URI if
the correct syntax for post dial, service provider, phone context,
etc has been used - otherwise the regex could always classify them
as a I<future extension>.

=head1 REFERENCES

=over 4

=item B<[RFC 1035]>

Mockapetris, P.: I<DOMAIN NAMES - IMPLEMENTATION AND SPECIFICATION>.
November 1987.

=item B<[RFC 2396]>

Berners-Lee, Tim, Fielding, R., and Masinter, L.: I<Uniform Resource
Identifiers (URI): Generic Syntax>. August 1998.

=item B<[RFC 2806]>

Vaha-Sipila, A.: I<URLs for Telephone Calls>. April 2000.

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
