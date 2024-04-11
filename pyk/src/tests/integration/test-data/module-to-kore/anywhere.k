module ANYWHERE-SYNTAX
    syntax Foo ::= "foo" | "bar"
endmodule

module ANYWHERE
    imports ANYWHERE-SYNTAX
    rule foo => bar [anywhere]
endmodule
