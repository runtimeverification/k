module TEST
  imports DOMAINS

  configuration <k> $PGM:Val </k>

  syntax Val ::= "inc" Int

  rule <k> inc I:Int => I +Int 1 ... </k>

endmodule

