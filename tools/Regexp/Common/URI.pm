package Regexp::Common::URI;

use Regexp::Common qw /pattern clean no_defaults/;

use strict;
use warnings;

use Exporter ();
use vars qw /@EXPORT_OK @ISA/;

@ISA       = qw /Exporter/;
@EXPORT_OK = qw /register_uri/;

use Regexp::Common qw /pattern clean no_defaults/;

use strict;
use warnings;

use vars qw /$VERSION/;
$VERSION = '2010010201';

# Use 'require' here, not 'use', so we delay running them after we are compiled.
# We also do it using an 'eval'; this saves us from have repeated similar
# lines. The eval is further explained in 'perldoc -f require'.
my @uris = qw /fax file ftp gopher http pop prospero news tel telnet tv wais/;
foreach my $uri (@uris) {
    eval "require Regexp::Common::URI::$uri";
    die $@ if $@;
}

my %uris;

sub register_uri {
    my ($scheme, $uri) = @_;
    $uris {$scheme} = $uri;
}

pattern name    => [qw (URI)],
        create  => sub {my $uri =  join '|' => values %uris;
                           $uri =~ s/\(\?k:/(?:/g;
                      "(?k:$uri)";
        },
        ;

1;

__END__

=pod

=head1 NAME

Regexp::Common::URI -- provide patterns for URIs.

=head1 SYNOPSIS

    use Regexp::Common qw /URI/;

    while (<>) {
        /$RE{URI}{HTTP}/       and  print "Contains an HTTP URI.\n";
    }

=head1 DESCRIPTION

Patterns for the following URIs are supported: fax, file, FTP, gopher,
HTTP, news, NTTP, pop, prospero, tel, telnet, tv and WAIS.
Each is documented in the I<Regexp::Common::URI::B<scheme>>,
manual page, for the appropriate scheme (in lowercase), except for
I<NNTP> URIs which are found in I<Regexp::Common::URI::news>.

=head2 C<$RE{URI}>

Return a pattern that recognizes any of the supported URIs. With
C<{-keep}>, only the entire URI is returned (in C<$1>).

=head1 REFERENCES

=over 4

=item B<[DRAFT-URI-TV]>

Zigmond, D. and Vickers, M: I<Uniform Resource Identifiers for
Television Broadcasts>. December 2000.

=item B<[DRAFT-URL-FTP]>

Casey, James: I<A FTP URL Format>. November 1996.

=item B<[RFC 1035]>

Mockapetris, P.: I<DOMAIN NAMES - IMPLEMENTATION AND SPECIFICATION>.
November 1987.

=item B<[RFC 1738]>

Berners-Lee, Tim, Masinter, L., McCahill, M.: I<Uniform Resource
Locators (URL)>. December 1994.

=item B<[RFC 2396]>

Berners-Lee, Tim, Fielding, R., and Masinter, L.: I<Uniform Resource
Identifiers (URI): Generic Syntax>. August 1998.

=item B<[RFC 2616]>

Fielding, R., Gettys, J., Mogul, J., Frystyk, H., Masinter, L., 
Leach, P. and Berners-Lee, Tim: I<Hypertext Transfer Protocol -- HTTP/1.1>.
June 1999.

=item B<[RFC 2806]>

Vaha-Sipila, A.: I<URLs for Telephone Calls>. April 2000.

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
