module TEST-SYNTAX
  imports INT-SYNTAX

  syntax Exp ::= Val
               | Exp "+" Exp
               | foo(Exp)
  syntax Val ::= foo(Val)
               | Int

endmodule

module TEST
  imports TEST-SYNTAX

  configuration <k> $PGM:Exp </k>

endmodule
