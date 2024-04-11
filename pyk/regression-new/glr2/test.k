// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module TEST-SYNTAX
  imports INT-SYNTAX

  syntax Exp ::= Val
               | Exp "+" Exp
               | foo(Exp) [klabel(foo)]
  syntax Val ::= foo(Val) [klabel(foo)]
               | Int

endmodule

module TEST
  imports TEST-SYNTAX

  configuration <k> $PGM:Exp </k>

endmodule
