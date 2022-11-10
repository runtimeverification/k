// Copyright (c) 2020 K Team. All Rights Reserved.

module TEST-SYNTAX
endmodule

module TEST
    imports TEST-SYNTAX
    imports BOOL
    imports INT

    configuration <k> $PGM:KItem </k>

    syntax KItem ::= runLemma ( Step ) | doneLemma ( Step )
 // -------------------------------------------------------
    rule <k> runLemma(S) => doneLemma(S) ... </k>

    syntax Step ::= Int
 // -------------------

    syntax FInt ::= FInt ( value: Int , one: Int ) [klabel(FInt), symbol]
 // ---------------------------------------------------------------------

    syntax FInt ::= "0FInt" "(" Int ")" [macro]
 // -------------------------------------------
    rule 0FInt(ONE) => FInt(0, ONE)

    syntax FInt ::= rdiv ( FInt , FInt ) [function]
 // -----------------------------------------------
    rule rdiv(FI1, FI2) => 0FInt(one(FI1)) requires value(FI2) ==Int 0

endmodule
