requires "domains.md"

module DEF-SYNTAX
    imports MAP
    imports BOOL

    syntax Foo ::= "a" | "b" | "c"
endmodule

module DEF
    imports DEF-SYNTAX

    rule <k> a => b ... </k>
endmodule
