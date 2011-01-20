package Regexp::Common::URI::RFC1035;

use Regexp::Common qw /pattern clean no_defaults/;

use strict;
use warnings;

use vars qw /$VERSION/;
$VERSION = '2010010201';

use vars qw /@EXPORT @EXPORT_OK %EXPORT_TAGS @ISA/;

use Exporter ();
@ISA = qw /Exporter/;

my %vars;

BEGIN {
    $vars {low}     = [qw /$digit $letter $let_dig $let_dig_hyp $ldh_str/];
    $vars {parts}   = [qw /$label $subdomain/];
    $vars {domain}  = [qw /$domain/];
}

use vars map {@$_} values %vars;

@EXPORT      = qw /$host/;
@EXPORT_OK   = map {@$_} values %vars;
%EXPORT_TAGS = (%vars, ALL => [@EXPORT_OK]);

# RFC 1035.
$digit             = "[0-9]";
$letter            = "[A-Za-z]";
$let_dig           = "[A-Za-z0-9]";
$let_dig_hyp       = "[-A-Za-z0-9]";
$ldh_str           = "(?:[-A-Za-z0-9]+)";
$label             = "(?:$letter(?:(?:$ldh_str){0,61}$let_dig)?)";
$subdomain         = "(?:$label(?:[.]$label)*)";
$domain            = "(?: |(?:$subdomain))";


1;

__END__

=pod

=head1 NAME

Regexp::Common::URI::RFC1035 -- Definitions from RFC1035;

=head1 SYNOPSIS

    use Regexp::Common::URI::RFC1035 qw /:ALL/;

=head1 DESCRIPTION

This package exports definitions from RFC1035. It's intended
usage is for Regexp::Common::URI submodules only. Its interface
might change without notice.

=head1 REFERENCES

=over 4

=item B<[RFC 1035]>

Mockapetris, P.: I<DOMAIN NAMES - IMPLEMENTATION AND SPECIFICATION>.
November 1987.

=back

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
