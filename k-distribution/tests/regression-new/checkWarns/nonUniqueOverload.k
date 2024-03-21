module NONUNIQUEOVERLOAD-SYNTAX
endmodule

module WARNS
  syntax Foo1 ::= Foo2

  syntax Foo1 ::= "foo" Foo1 [overload(foo), unused]
  syntax Foo2 ::= "foo" Foo2 [overload(foo), unused]

  syntax Foo1 ::= "foo" Foo1 Foo1 [overload(foo), unused]
  syntax Foo2 ::= "foo" Foo2 Foo2 [overload(foo), unused]
endmodule

module NOWARNS
  imports DOMAINS

  syntax Exp  ::= Int | Id

  syntax Exps ::= List{Exp, ","} [overload(exps), unused]
  syntax Ids  ::= List{Id, ","}  [overload(exps), unused]

  syntax Exps ::= Ids
endmodule

module NONUNIQUEOVERLOAD
  imports WARNS
  imports NOWARNS
endmodule
