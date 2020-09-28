module TEST-SYNTAX
  imports INT-SYNTAX

  syntax Exp ::= Val
               | Exp "+" Exp
               | foo(Exp, Exp, Int)
  syntax Val ::= foo(Val, Val, Int)
               | Int

endmodule

module TEST
  imports TEST-SYNTAX

  configuration <k> $PGM:Exp </k>

endmodule
