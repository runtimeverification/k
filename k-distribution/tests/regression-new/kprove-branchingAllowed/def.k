module DEF-SYNTAX
    imports MAP
    imports BOOL

    syntax Foo ::= "a" | "b" | "c" | "d"

    configuration <k> $PGM:Foo </k>

    rule <k> a => b </k>
    rule <k> a => c </k>
    rule <k> b => d </k>
    rule <k> c => d </k>

endmodule

module DEF
    imports DEF-SYNTAX
endmodule
