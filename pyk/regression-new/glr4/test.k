// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module TEST-SYNTAX
  imports INT-SYNTAX

  syntax Exp5 ::= Exp4 | Exp5 "-" Exp5 | foo(Exp5) [klabel(foo)]
  syntax Exp4 ::= Exp3 | Exp4 "-" Exp4 | foo(Exp4) [klabel(foo)]
  syntax Exp3 ::= Exp2 | Exp3 "-" Exp3 | foo(Exp3) [klabel(foo)]
  syntax Exp2 ::= Exp | Exp2 "-" Exp2 | foo(Exp2) [klabel(foo)]
  syntax Exp ::= Val
               | Exp "+" Exp
               | foo(Exp) [klabel(foo)]
  syntax Val ::= foo(Val) [klabel(foo)]
               | Int

endmodule

module TEST
  imports TEST-SYNTAX

  configuration <k> $PGM:Exp5 </k>

endmodule
