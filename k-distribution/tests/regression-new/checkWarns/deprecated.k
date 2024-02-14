module DEPRECATED-SYNTAX
endmodule

module DEPRECATED
  imports BOOL
  syntax Foo ::= foo() [deprecated]
               | bar() [deprecated]
               | baz(Foo)
               | qux(Foo) [deprecated]

  syntax Bool ::= f() [function, deprecated]
  rule f() => true

  rule baz(baz(foo())) => baz(bar())
    requires f()
    ensures f()

  context [qux]: qux(HOLE) requires f()
  context alias [qux2]: baz(qux(HERE)) requires f()

  syntax KResult ::= Foo

  configuration
    <k> qux(foo()) </k>
endmodule
