module TEST
  imports INT
  imports BOOL
  imports LIST

  configuration <k> $PGM:Pgm </k>

  syntax Pgm ::= foo() | Pgm2
  syntax Pgm2 ::= bar(baz: Int)

  rule foo() => ?X:Pgm2
  rule X:Pgm2 => baz(X)
  rule I:Int => false

endmodule
