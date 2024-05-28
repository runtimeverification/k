requires "domains.md"

module CUSTOM-STEP-SYNTAX

    syntax KItem ::= Step
    syntax Step ::= "a" | "b" | "c" | "d"
    
endmodule

module CUSTOM-STEP
    imports CUSTOM-STEP-SYNTAX
    imports K-EQUAL
    configuration <k> $PGM:KItem </k>

    rule [a.b]: <k> a => b ... </k>
    rule [b.c]: <k> b => c ... </k>
    rule [c.d]: <k> c => d ... </k>

endmodule