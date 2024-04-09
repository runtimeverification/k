// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module MACROWITHFUNCTION
    imports INT
    imports BOOL

    configuration <k> $PGM:Pgm </k>

    syntax FInt ::= FInt ( value: Int , one: Int ) [klabel(FInt), symbol]
 // ---------------------------------------------------------------------

    syntax Wad = FInt
    syntax Wad ::= wad ( Int ) [macro]
 // --------------------------
    rule wad(I) => FInt(I *Int WAD, WAD)

    syntax Int ::= "WAD" [macro]
 // --------------------
    rule WAD => 1000000000000000000

    syntax Pgm ::= "go" FInt | Pgm ";" Pgm [left]
 // ---------------------------------------------
    rule <k> P ; Q => P ~> Q ... </k>
    rule <k> go wad(0) => . ... </k>
endmodule
