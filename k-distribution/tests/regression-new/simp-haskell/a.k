module A
  import INT
  syntax Int ::= abs(Int) [function, functional]
               | "error" [function, functional]
  rule abs(X:Int) => X:Int requires X >Int 0
  rule abs(X) => 0 -Int X [owise]

  rule abs(0) => error [simplification]

  configuration <k> $PGM:Int </k>
endmodule
