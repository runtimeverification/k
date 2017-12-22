module LANG-SYNTAX
    syntax Widget ::= "A" | "B" | "C"
    syntax Stmt   ::= "const" Widget Widget
endmodule

module LANG
    imports LANG-SYNTAX

    configuration <k>$PGM:Stmt</k>
    rule const X Y => ret X
    syntax Stmt ::= "ret" Widget
    rule ret   X   => X
endmodule
