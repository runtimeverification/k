module TEST
  imports INT

configuration <k> $PGM:K </k> <foo> .K </foo>

  syntax Foo ::= bar() | baz(Foo)
  syntax Foo ::= Int
  rule bar() => 0
  syntax KResult ::= Int
  context <k> baz(HOLE) ... </k> <foo> .K </foo>
endmodule
