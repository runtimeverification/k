// Copyright (c) 2013-2016 K Team. All Rights Reserved.

require "substitution.k"

module LAMBDA
  imports SUBSTITUTION

  syntax Val ::= Id
               | "lambda" Id "." Exp  [binder]
  syntax Exp ::= Val
               | Exp Exp              [left]
               | "(" Exp ")"          [bracket]
  syntax KVariable ::= Id

  rule (lambda X:Id . E:Exp) V:Val => E[V / X]   [anywhere]
endmodule
