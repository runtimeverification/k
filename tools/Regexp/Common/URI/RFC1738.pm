package Regexp::Common::URI::RFC1738;

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
    $vars {low}     = [qw /$digit $digits $hialpha $lowalpha $alpha $alphadigit
                           $safe $extra $national $punctuation $unreserved
                           $unreserved_range $reserved $uchar $uchars $xchar
                           $xchars $hex $escape/];

    $vars {connect} = [qw /$port $hostnumber $toplabel $domainlabel $hostname
                           $host $hostport $user $password $login/];

    $vars {parts}   = [qw /$fsegment $fpath $group $article $grouppart
                           $search $database $wtype $wpath $psegment
                           $fieldname $fieldvalue $fieldspec $ppath/];
}

use vars map {@$_} values %vars;

@EXPORT      = qw /$host/;
@EXPORT_OK   = map {@$_} values %vars;
%EXPORT_TAGS = (%vars, ALL => [@EXPORT_OK]);

# RFC 1738, base definitions.

# Lowlevel definitions.
$digit             =  '[0-9]';
$digits            =  '[0-9]+';
$hialpha           =  '[A-Z]';
$lowalpha          =  '[a-z]';
$alpha             =  '[a-zA-Z]';                 # lowalpha | hialpha
$alphadigit        =  '[a-zA-Z0-9]';              # alpha    | digit
$safe              =  '[-$_.+]';
$extra             =  "[!*'(),]";
$national          =  '[][{}|\\^~`]';
$punctuation       =  '[<>#%"]';
$unreserved_range  = q [-a-zA-Z0-9$_.+!*'(),];  # alphadigit | safe | extra
$unreserved        =  "[$unreserved_range]";
$reserved          =  '[;/?:@&=]';
$hex               =  '[a-fA-F0-9]';
$escape            =  "(?:%$hex$hex)";
$uchar             =  "(?:$unreserved|$escape)";
$uchars            =  "(?:(?:$unreserved|$escape)*)";
$xchar             =  "(?:[$unreserved_range;/?:\@&=]|$escape)";
$xchars            =  "(?:(?:[$unreserved_range;/?:\@&=]|$escape)*)";

# Connection related stuff.
$port              =  "(?:$digits)";
$hostnumber        =  "(?:$digits\[.]$digits\[.]$digits\[.]$digits)";
$toplabel          =  "(?:$alpha\[-a-zA-Z0-9]*$alphadigit|$alpha)";
$domainlabel       =  "(?:(?:$alphadigit\[-a-zA-Z0-9]*)?$alphadigit)";
$hostname          =  "(?:(?:$domainlabel\[.])*$toplabel)";
$host              =  "(?:$hostname|$hostnumber)";
$hostport          =  "(?:$host(?::$port)?)";

$user              =  "(?:(?:[$unreserved_range;?&=]|$escape)*)";
$password          =  "(?:(?:[$unreserved_range;?&=]|$escape)*)";
$login             =  "(?:(?:$user(?::$password)?\@)?$hostport)";

# Parts (might require more if we add more URIs).

# FTP/file
$fsegment          =  "(?:(?:[$unreserved_range:\@&=]|$escape)*)";
$fpath             =  "(?:$fsegment(?:/$fsegment)*)";

# NNTP/news.
$group             =  "(?:$alpha\[-A-Za-z0-9.+_]*)";
$article           =  "(?:(?:[$unreserved_range;/?:&=]|$escape)+" .
                      '@' . "$host)";
$grouppart         =  "(?:[*]|$article|$group)"; # It's important that
                                                 # $article goes before
                                                 # $group.

# WAIS.
$search            =  "(?:(?:[$unreserved_range;:\@&=]|$escape)*)";
$database          =  $uchars;
$wtype             =  $uchars;
$wpath             =  $uchars;

# prospero
$psegment          =  "(?:(?:[$unreserved_range?:\@&=]|$escape)*)";
$fieldname         =  "(?:(?:[$unreserved_range?:\@&]|$escape)*)";
$fieldvalue        =  "(?:(?:[$unreserved_range?:\@&]|$escape)*)";
$fieldspec         =  "(?:;$fieldname=$fieldvalue)";
$ppath             =  "(?:$psegment(?:/$psegment)*)";

#
# The various '(?:(?:[$unreserved_range ...]|$escape)*)' above need
# some loop unrolling to speed up the match.
#

1;

__END__

=pod

=head1 NAME

Regexp::Common::URI::RFC1738 -- Definitions from RFC1738;

=head1 SYNOPSIS

    use Regexp::Common::URI::RFC1738 qw /:ALL/;

=head1 DESCRIPTION

This package exports definitions from RFC1738. It's intended
usage is for Regexp::Common::URI submodules only. Its interface
might change without notice.

=head1 REFERENCES

=over 4

=item B<[RFC 1738]>

Berners-Lee, Tim, Masinter, L., McCahill, M.: I<Uniform Resource
Locators (URL)>. December 1994.

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
