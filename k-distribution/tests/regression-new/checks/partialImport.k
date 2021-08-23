module PARTIALIMPORT
  imports A

  rule foo() => .K
  rule bar() => .K
  rule alsoAFoo() => .K
endmodule

module A
  imports B.foo
endmodule

module B
  imports C
  syntax Foo ::= foo()
  syntax Bar ::= bar()
endmodule

module C
  syntax Foo ::= alsoAFoo() [foo]
endmodule
