// Copyright (c) 2012-2015 K Team. All Rights Reserved.
require "domains.k"

module LAMBDA
  imports DOMAINS-SYNTAX

  syntax Val ::= Id
               | "lambda" Id "." Exp
  syntax Exp ::= Val
               | Exp Exp      [left]
               | "(" Exp ")"  [bracket]
endmodule
