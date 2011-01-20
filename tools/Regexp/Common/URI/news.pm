package Regexp::Common::URI::news;

use Regexp::Common               qw /pattern clean no_defaults/;
use Regexp::Common::URI          qw /register_uri/;
use Regexp::Common::URI::RFC1738 qw /$grouppart $group $article
                                     $host $port $digits/;

use strict;
use warnings;

use vars qw /$VERSION/;
$VERSION = '2010010201';


my $news_scheme = 'news';
my $news_uri    = "(?k:(?k:$news_scheme):(?k:$grouppart))";

my $nntp_scheme = 'nntp';
my $nntp_uri    = "(?k:(?k:$nntp_scheme)://(?k:(?k:(?k:$host)(?::(?k:$port))?)" 
                . "/(?k:$group)(?:/(?k:$digits))?))";

register_uri $news_scheme => $news_uri;
register_uri $nntp_scheme => $nntp_uri;

pattern name    => [qw (URI news)],
        create  => $news_uri,
        ;

pattern name    => [qw (URI NNTP)],
        create  => $nntp_uri,
        ;

1;

__END__

=pod

=head1 NAME

Regexp::Common::URI::news -- Returns a pattern for file URIs.

=head1 SYNOPSIS

    use Regexp::Common qw /URI/;

    while (<>) {
        /$RE{URI}{news}/       and  print "Contains a news URI.\n";
    }

=head1 DESCRIPTION

=head2 $RE{URI}{news}

Returns a pattern that matches I<news> URIs, as defined by RFC 1738.
News URIs have the form:

    "news:" ( "*" | group | article "@" host )

Under C<{-keep}>, the following are returned:

=over 4

=item $1

The complete URI.

=item $2

The scheme.

=item $3

The part of the URI following "news://".

=back

=head2 $RE{URI}{NNTP}

Returns a pattern that matches I<NNTP> URIs, as defined by RFC 1738.
NNTP URIs have the form:

    "nntp://" host [ ":" port ] "/" group [ "/" digits ]

Under C<{-keep}>, the following are returned:

=over 4

=item $1

The complete URI.

=item $2

The scheme.

=item $3

The part of the URI following "nntp://".

=item $4

The host and port, separated by a colon. If no port was given, just
the host.

=item $5

The host.

=item $6

The port, if given.

=item $7

The group.

=item $8

The digits, if given.

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
