# TV URLs. 
# Internet draft: draft-zigmond-tv-url-03.txt

package Regexp::Common::URI::tv;

use Regexp::Common               qw /pattern clean no_defaults/;
use Regexp::Common::URI          qw /register_uri/;
use Regexp::Common::URI::RFC2396 qw /$hostname/;

use strict;
use warnings;

use vars qw /$VERSION/;
$VERSION = '2010010201';


my $tv_scheme = 'tv';
my $tv_url    = "(?k:(?k:$tv_scheme):(?k:$hostname)?)";

register_uri $tv_scheme => $tv_url;

pattern name    => [qw (URI tv)],
        create  => $tv_url,
        ;

1;

__END__

=pod

=head1 NAME

Regexp::Common::URI::tv -- Returns a pattern for tv URIs.

=head1 SYNOPSIS

    use Regexp::Common qw /URI/;

    while (<>) {
        /$RE{URI}{tv}/       and  print "Contains a tv URI.\n";
    }

=head1 DESCRIPTION

=head2 C<$RE{URI}{tv}>

Returns a pattern that recognizes TV uris as per an Internet draft
[DRAFT-URI-TV].

Under C<{-keep}>, the following are returned:

=over 4

=item $1

The entire URI.

=item $2

The scheme.

=item $3

The host.

=back

=head1 REFERENCES

=over 4

=item B<[DRAFT-URI-TV]>

Zigmond, D. and Vickers, M: I<Uniform Resource Identifiers for
Television Broadcasts>. December 2000.

=item B<[RFC 2396]>

Berners-Lee, Tim, Fielding, R., and Masinter, L.: I<Uniform Resource
Identifiers (URI): Generic Syntax>. August 1998.

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
