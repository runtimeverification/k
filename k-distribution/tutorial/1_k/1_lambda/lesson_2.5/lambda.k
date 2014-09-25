// Copyright (c) 2013-2014 K Team. All Rights Reserved.
require "modules/substitution.k"

module LAMBDA
  imports SUBSTITUTION

  syntax Val ::= Id
               | "lambda" Id "." Exp  [binder]
  syntax Exp ::= Val
               | Exp Exp              [left]
               | "(" Exp ")"          [bracket]

  rule (lambda X:Id . E:Exp) V:Val => E[V / X]   [anywhere]
endmodule
