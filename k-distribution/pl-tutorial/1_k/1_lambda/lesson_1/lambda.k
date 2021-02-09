// Copyright (c) 2012-2019 K Team. All Rights Reserved.

module LAMBDA-SYNTAX
  imports DOMAINS-SYNTAX

  syntax Val ::= Id
               | "lambda" Id "." Exp
  syntax Exp ::= Val
               | Exp Exp      [left]
               | "(" Exp ")"  [bracket]
endmodule

module LAMBDA
  imports LAMBDA-SYNTAX
endmodule
