module NONUNIQUEOVERLOAD-SYNTAX
endmodule

module NONUNIQUEOVERLOAD
    syntax Foo1 ::= Foo2

    syntax Foo1 ::= "foo" Foo1 [overload(foo), unused]
    syntax Foo2 ::= "foo" Foo2 [overload(foo), unused]

    syntax Foo1 ::= "foo" Foo1 Foo1 [overload(foo), unused]
    syntax Foo2 ::= "foo" Foo2 Foo2 [overload(foo), unused]
endmodule
