// Copyright (c) 2013-2015 K Team. All Rights Reserved.
require "modules/substitution.k"

module LAMBDA
  imports SUBSTITUTION

  syntax Val ::= Id
               | "lambda" Id "." Exp  [binder]
  syntax Exp ::= Val
               | Exp Exp              [left]
               | "(" Exp ")"          [bracket]
  syntax Variable ::= Id

  rule (lambda X:Id . E:Exp) V:Val => E[V / X]   [anywhere]
endmodule
