module HOOK-SYNTAX
    syntax Foo ::= "foo" [hook(foo)]
endmodule

module HOOK
    imports HOOK-SYNTAX
endmodule
