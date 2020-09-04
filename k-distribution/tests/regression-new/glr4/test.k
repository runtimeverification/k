module TEST-SYNTAX
  imports INT-SYNTAX

  syntax Exp5 ::= Exp4 | Exp5 "-" Exp5 | foo(Exp5)
  syntax Exp4 ::= Exp3 | Exp4 "-" Exp4 | foo(Exp4)
  syntax Exp3 ::= Exp2 | Exp3 "-" Exp3 | foo(Exp3)
  syntax Exp2 ::= Exp | Exp2 "-" Exp2 | foo(Exp2)
  syntax Exp ::= Val
               | Exp "+" Exp
               | foo(Exp)
  syntax Val ::= foo(Val)
               | Int

endmodule

module TEST
  imports TEST-SYNTAX

  configuration <k> $PGM:Exp5 </k>

endmodule
