// Copyright (c) 2012-2014 K Team. All Rights Reserved.
require "modules/substitution.k"

module LAMBDA
  imports SUBSTITUTION

  syntax Val ::= Id
               | "lambda" Id "." Exp  [binder, latex(\lambda{#1}.{#2})]
  syntax Exp ::= Val
               | Exp Exp              [strict, left]
               | "(" Exp ")"          [bracket]
  syntax KResult ::= Val

  rule (lambda X:Id . E:Exp) V:Val => E[V / X]
endmodule
