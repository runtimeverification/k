package Regexp::Common::URI::RFC2384;


use Regexp::Common qw /pattern clean no_defaults/;
use Regexp::Common::URI::RFC1738 qw /$unreserved_range $escape $hostport/;

use strict;
use warnings;

use vars qw /$VERSION/;
$VERSION = '2010010201';

use vars qw /@EXPORT @EXPORT_OK %EXPORT_TAGS @ISA/;

use Exporter ();
@ISA = qw /Exporter/;


my %vars;

BEGIN {
    $vars {low}     = [qw /$achar_range $achar $achars $achar_more/];
    $vars {connect} = [qw /$enc_sasl $enc_user $enc_ext $enc_auth_type $auth
                           $user_auth $server/];
    $vars {parts}   = [qw /$pop_url/];
}

use vars map {@$_} values %vars;

@EXPORT      = qw /$host/;
@EXPORT_OK   = map {@$_} values %vars;
%EXPORT_TAGS = (%vars, ALL => [@EXPORT_OK]);

# RFC 2384, POP3.

# Lowlevel definitions.
$achar_range       =  "$unreserved_range&=~";
$achar             =  "(?:[$achar_range]|$escape)";
$achars            =  "(?:(?:[$achar_range]+|$escape)*)";
$achar_more        =  "(?:(?:[$achar_range]+|$escape)+)";
$enc_sasl          =  $achar_more;
$enc_user          =  $achar_more;
$enc_ext           =  "(?:[+](?:APOP|$achar_more))";
$enc_auth_type     =  "(?:$enc_sasl|$enc_ext)";
$auth              =  "(?:;AUTH=(?:[*]|$enc_auth_type))";
$user_auth         =  "(?:$enc_user$auth?)";
$server            =  "(?:(?:$user_auth\@)?$hostport)";
$pop_url           =  "(?:pop://$server)";


1;

__END__

=pod

=head1 NAME

Regexp::Common::URI::RFC2384 -- Definitions from RFC2384;

=head1 SYNOPSIS

    use Regexp::Common::URI::RFC2384 qw /:ALL/;

=head1 DESCRIPTION

This package exports definitions from RFC2384. It's intended
usage is for Regexp::Common::URI submodules only. Its interface
might change without notice.

=head1 REFERENCES

=over 4

=item B<[RFC 2384]>

Gellens, R.: I<POP URL scheme> August 1998.

=back

=head1 AUTHOR

Abigail S<(I<regexp-common@abigail.be>)>.

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
