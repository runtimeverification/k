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
    rule <k> a => b </k> requires #let _ = 1 #in true
    rule <k> #let _ = 1 #in true => 2 </k>
    rule <k> 1 => #let _ = 1 #in true </k>
    rule <k> a => b </k> requires #let #let _ = 2 #in true = 1 #in true
    rule <k> 1 => 2 </k> requires #fun ( _ => true ) ( 1 )
    rule <k> (1 => 2) ~> #fun ( _ => 2 ) ( 2 ) </k>
    rule <k> 1 => 2 </k> requires #fun ( _ => #let _ = 1 #in true ) ( 1 )
    rule <k> 1 => 2 </k> requires #fun ( #let _ = 1 #in true => true ) ( 5 )
endmodule
