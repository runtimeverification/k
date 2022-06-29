// This should kompile just fine for the haskell backend, variables
// in the requires clause should be considered as part of LHS for haskell backend.
// https://github.com/runtimeverification/k/issues/2687

module CHECKRHSHASKELL-SYNTAX

endmodule

module CHECKRHSHASKELL
    imports CHECKRHSHASKELL-SYNTAX
    imports MAP
    imports INT
    imports BOOL

    syntax Pgm ::= "a" | "b"

    rule <k> a => b </k>

    syntax Int ::= f ( Int ) [function, functional, no-evaluators]

    configuration <k> $PGM:Pgm </k>

    rule <k> a => b </k> requires f(_X) ==Int 3

endmodule
