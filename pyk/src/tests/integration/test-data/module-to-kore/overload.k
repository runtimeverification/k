module OVERLOAD-SYNTAX
    syntax Foo ::= Bar
    syntax Foo ::= Baz
    syntax Baz ::= Qux
    syntax Foo ::= foo ( Foo , Foo ) [overload(foo)]
    syntax Foo ::= foo ( Bar , Foo ) [overload(foo)]
    syntax Bar ::= foo ( Foo , Foo ) [overload(foo)]
    syntax Baz ::= foo ( Baz , Foo ) [overload(foo)]
    syntax Qux ::= foo ( Baz , Qux ) [overload(foo)]
endmodule

module OVERLOAD
    imports OVERLOAD-SYNTAX
endmodule
