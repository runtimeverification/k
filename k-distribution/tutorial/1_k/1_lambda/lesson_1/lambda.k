// Copyright (c) 2012-2019 K Team. All Rights Reserved.

module LAMBDA
  imports DOMAINS

  syntax Val ::= Id
               | "lambda" Id "." Exp
  syntax Exp ::= Val
               | Exp Exp      [left]
               | "(" Exp ")"  [bracket]
endmodule
