module OVERLOAD
    syntax Foo ::= Bar
    syntax Foo ::= Baz
    syntax Baz ::= Qux
    syntax Foo ::= foo ( Foo , Foo ) [overload(foo)]
    syntax Bar ::= foo ( Foo , Bar ) [overload(foo)]
    syntax Baz ::= foo ( Baz , Foo ) [overload(foo)]
    syntax Qux ::= foo ( Baz , Qux ) [overload(foo)]
endmodule
