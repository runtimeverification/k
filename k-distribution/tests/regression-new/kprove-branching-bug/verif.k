// Copyright (c) 2020 K Team. All Rights Reserved.

module VERIF
    imports DOMAINS

    configuration <k> $PGM:Pgm </k>

    syntax Pgm ::= "step" Int
    rule <k> step I => . ...</k>
      requires I <Int 1
    rule <k> step I => . ...</k>
      requires I ==Int 1

    syntax Int ::= foo( Int )       [function, smtlib(foo)]
    rule foo(I) => I %Int 2         [concrete]
    rule foo(_) <Int 2 => true      [simplification]

endmodule
