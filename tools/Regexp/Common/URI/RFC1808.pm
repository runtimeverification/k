package Regexp::Common::URI::RFC1808;

BEGIN {
    # This makes sure 'use warnings' doesn't bomb out on 5.005_*;
    # warnings won't be enabled on those old versions though.
    if ($] < 5.006 && !exists $INC {"warnings.pm"}) {
        $INC {"warnings.pm"} = 1;
        no strict 'refs';
        *{"warnings::unimport"} = sub {0};
    }
}

use strict;
use warnings;

use vars qw /$VERSION/;
$VERSION = '2010010201';

use vars qw /@EXPORT @EXPORT_OK %EXPORT_TAGS @ISA/;

use Exporter ();
@ISA = qw /Exporter/;


my %vars;

BEGIN {
    $vars {low}     = [qw /$punctuation $reserved_range $reserved $national
                           $extra $safe $digit $digits $hialpha $lowalpha
                           $alpha $alphadigit $hex $escape $unreserved_range
                           $unreserved $uchar $uchars $pchar_range $pchar
                           $pchars/],

    $vars {parts}   = [qw /$fragment $query $param $params $segment
                           $fsegment $path $net_loc $scheme $rel_path
                           $abs_path $net_path $relativeURL $generic_RL
                           $absoluteURL $URL/],
}

use vars map {@$_} values %vars;

@EXPORT      = qw /$host/;
@EXPORT_OK   = map {@$_} values %vars;
%EXPORT_TAGS = (%vars, ALL => [@EXPORT_OK]);

# RFC 1808, base definitions.

# Lowlevel definitions.
$punctuation       =  '[<>#%"]';
$reserved_range    = q [;/?:@&=];
$reserved          =  "[$reserved_range]";
$national          =  '[][{}|\\^~`]';
$extra             =  "[!*'(),]";
$safe              =  '[-$_.+]';

$digit             =  '[0-9]';
$digits            =  '[0-9]+';
$hialpha           =  '[A-Z]';
$lowalpha          =  '[a-z]';
$alpha             =  '[a-zA-Z]';                 # lowalpha | hialpha
$alphadigit        =  '[a-zA-Z0-9]';              # alpha    | digit

$hex               =  '[a-fA-F0-9]';
$escape            =  "(?:%$hex$hex)";

$unreserved_range  = q [-a-zA-Z0-9$_.+!*'(),];  # alphadigit | safe | extra
$unreserved        =  "[$unreserved_range]";
$uchar             =  "(?:$unreserved|$escape)";
$uchars            =  "(?:(?:$unreserved+|$escape)*)";

$pchar_range       = qq [$unreserved_range:\@&=];
$pchar             =  "(?:[$pchar_range]|$escape)";
$pchars            =  "(?:(?:[$pchar_range]+|$escape)*)";


# Parts
$fragment          =  "(?:(?:[$unreserved_range$reserved_range]+|$escape)*)";
$query             =  "(?:(?:[$unreserved_range$reserved_range]+|$escape)*)";

$param             =  "(?:(?:[$pchar_range/]+|$escape)*)";
$params            =  "(?:$param(?:;$param)*)";

$segment           =  "(?:(?:[$pchar_range]+|$escape)*)";
$fsegment          =  "(?:(?:[$pchar_range]+|$escape)+)";
$path              =  "(?:$fsegment(?:/$segment)*)";

$net_loc           =  "(?:(?:[$pchar_range;?]+|$escape)*)";
$scheme            =  "(?:(?:[-a-zA-Z0-9+.]+|$escape)+)";

$rel_path          =  "(?:$path?(?:;$params)?(?:?$query)?)";
$abs_path          =  "(?:/$rel_path)";
$net_path          =  "(?://$net_loc$abs_path?)";

$relativeURL       =  "(?:$net_path|$abs_path|$rel_path)";
$generic_RL        =  "(?:$scheme:$relativeURL)";
$absoluteURL       =  "(?:$generic_RL|" .
                "(?:$scheme:(?:[$unreserved_range$reserved_range]+|$escape)*))";
$URL               =  "(?:(?:$absoluteURL|$relativeURL)(?:#$fragment)?)";


1;

__END__

=pod

=head1 NAME

Regexp::Common::URI::RFC1808 -- Definitions from RFC1808;

=head1 SYNOPSIS

    use Regexp::Common::URI::RFC1808 qw /:ALL/;

=head1 DESCRIPTION

This package exports definitions from RFC1808. It's intended
usage is for Regexp::Common::URI submodules only. Its interface
might change without notice.

=head1 REFERENCES

=over 4

=item B<[RFC 1808]>

Fielding, R.: I<Relative Uniform Resource Locators (URL)>. June 1995.

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
