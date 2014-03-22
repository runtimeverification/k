module TEST

  configuration <k> $PGM:Exps </k>
  syntax Exp ::= Id
               | Exp "+" Exp
  syntax Exps ::= NeList{Exp,","}

endmodule