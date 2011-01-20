package Regexp::Common::_support;

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

#
# Returns true/false, depending whether the given the argument
# satisfies the LUHN checksum.
# See http://www.webopedia.com/TERM/L/Luhn_formula.html.
#
# Note that this function is intended to be called from regular
# expression, so it should NOT use a regular expression in any way.
#
sub luhn {
    my $arg  = shift;
    my $even = 0;
    my $sum  = 0;
    while (length $arg) {
        my $num = chop $arg;
        return if $num lt '0' || $num gt '9';
        if ($even && (($num *= 2) > 9)) {$num = 1 + ($num % 10)}
        $even = 1 - $even;
        $sum += $num;
    }
    !($sum % 10)
}

sub import {
    my $pack   = shift;
    my $caller = caller;
    no strict 'refs';
    *{$caller . "::" . $_} = \&{$pack . "::" . $_} for @_;
}


1;

__END__

=pod

=head1 NAME

Regexp::Common::support -- Support functions for Regexp::Common.

=head1 SYNOPSIS

    use Regexp::Common::_support qw /luhn/;

    luhn ($number)    # Returns true/false.


=head1 DESCRIPTION

This module contains some subroutines to be used by other C<Regexp::Common>
modules. It's not intended to be used directly. Subroutines from the 
module may disappear without any notice, or their meaning or interface
may change without notice.

=over 4

=item luhn

This subroutine returns true if its argument passes the luhn checksum test.

=back

=head1 SEE ALSO

L<http://www.webopedia.com/TERM/L/Luhn_formula.html>.

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
