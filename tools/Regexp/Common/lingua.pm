package Regexp::Common::lingua;

use Regexp::Common qw /pattern clean no_defaults/;

use strict;
use warnings;

use vars qw /$VERSION/;
$VERSION = '2010010201';


pattern name    => [qw /lingua palindrome -chars=[A-Za-z]/],
        create  => sub {
            use re 'eval';
            my $keep = exists $_ [1] -> {-keep};
            my $ch   = $_ [1] -> {-chars};
            my $idx  = $keep ? "1:$ch" : "0:$ch";
            my $r    = "(??{\$Regexp::Common::lingua::pd{'" . $idx . "'}})";
            $Regexp::Common::lingua::pd {$idx} = 
                    $keep ? qr /($ch|($ch)($r)?\2)/ : qr  /$ch|($ch)($r)?\1/;
        #   print "[$ch]: ", $Regexp::Common::lingua::pd {$idx}, "\n";
        #   $Regexp::Common::lingua::pd {$idx};
        },
        version => 5.006
        ;


1;

__END__

=pod

=head1 NAME

Regexp::Common::lingua -- provide regexes for language related stuff.

=head1 SYNOPSIS

    use Regexp::Common qw /lingua/;

    while (<>) {
        /^$RE{lingua}{palindrome}$/    and  print "is a palindrome\n";
    }


=head1 DESCRIPTION

Please consult the manual of L<Regexp::Common> for a general description
of the works of this interface.

Do not use this module directly, but load it via I<Regexp::Common>.

=head2 C<$RE{lingua}{palindrome}>

Returns a pattern that recognizes a palindrome, a string that is the
same if you reverse it. By default, it only matches strings consisting
of letters, but this can be changed using the C<{-chars}> option.
This option takes a character class (default is C<[A-Za-z]>) as
argument.

If C<{-keep}> is used, only C<$1> will be set, and set to the entire
match. 

This pattern requires at least perl 5.6.0.

=head1 SEE ALSO

L<Regexp::Common> for a general description of how to use this interface.

=head1 AUTHOR

Damian Conway (damian@conway.org)

=head1 MAINTAINANCE

This package is maintained by Abigail S<(I<regexp-common@abigail.be>)>.

=head1 BUGS AND IRRITATIONS

Many regexes are missing.
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
