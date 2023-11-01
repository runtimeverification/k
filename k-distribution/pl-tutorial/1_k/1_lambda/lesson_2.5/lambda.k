// Copyright (c) K Team. All Rights Reserved.

require "substitution.md"

module LAMBDA-SYNTAX
  imports DOMAINS-SYNTAX
  imports KVAR-SYNTAX

  syntax Val ::= KVar
               | "lambda" KVar "." Exp  [binder]
  syntax Exp ::= Val
               | Exp Exp              [left]
               | "(" Exp ")"          [bracket]
endmodule

module LAMBDA
  imports LAMBDA-SYNTAX
  imports SUBSTITUTION

  rule (lambda X:KVar . E:Exp) V:Val => E[V / X]   [anywhere]
endmodule
