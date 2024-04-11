// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module TEST-SYNTAX
  imports INT-SYNTAX

  syntax Exp ::= Val
               | Exp "+" Exp
               | foo(Exp, Exp, Int) [klabel(foo)]
  syntax Val ::= foo(Val, Val, Int) [klabel(foo)]
               | Int

endmodule

module TEST
  imports TEST-SYNTAX

  configuration <k> $PGM:Exp </k>

endmodule
