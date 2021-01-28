// Copyright (c) 2012-2019 K Team. All Rights Reserved.

require "substitution.md"

module LAMBDA-SYNTAX
  imports DOMAINS-SYNTAX
  imports KVAR-SYNTAX

  syntax Val ::= KVar
               | "lambda" KVar "." Exp  [binder, latex(\lambda{#1}.{#2})]
  syntax Exp ::= Val
               | Exp Exp              [strict, left]
               | "(" Exp ")"          [bracket]
endmodule

module LAMBDA
  imports LAMBDA-SYNTAX
  imports SUBSTITUTION

  syntax KResult ::= Val

  rule (lambda X:KVar . E:Exp) V:Val => E[V / X]
endmodule
