module TEST
  imports INT

  syntax Foo ::= test(Int, foo: Int, bar: Int)

  syntax Foo ::= incrementFoo(Foo) [function]
  syntax Foo ::= incrementBar(Foo) [function]

  rule incrementFoo(F) => #fun(test(... foo: N => N +Int 1))(F)
  rule incrementBar(F) => #fun(test(... bar: N => N +Int 1))(F)
endmodule
