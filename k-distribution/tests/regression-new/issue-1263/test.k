module TEST
    imports INT
    imports BOOL

    configuration <k> $PGM:Pgm </k>

    syntax FInt ::= FInt ( value: Int , one: Int ) [klabel(FInt), symbol]
 // ---------------------------------------------------------------------

    syntax Wad = FInt
    syntax Wad ::= wad ( Int ) [macro]
 // ----------------------------------

    // Note that if we just switch the order of these rules in the file, it works.
    // But we should not care about order of rules in the file, is better for user to be explicit.
    rule wad(I) => FInt(I *Int WAD, WAD) [priority(26)]
    rule wad(1) => FInt(WAD       , WAD) [priority(25)]
    rule wad(0) => FInt(0         , WAD) [priority(25)]

    syntax Int ::= "WAD" [macro]
 // ----------------------------
    rule WAD => 1000000000000000000

    syntax Pgm ::= "go" FInt | Pgm ";" Pgm [left]
 // ---------------------------------------------
    rule <k> P ; Q => P ~> Q ... </k>
    rule <k> go wad(0) => . ... </k>
endmodule
