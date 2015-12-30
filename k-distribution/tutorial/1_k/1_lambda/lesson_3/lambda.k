// Copyright (c) 2012-2015 K Team. All Rights Reserved.
require "domains.k"
require "substitution.k"

module LAMBDA-SYNTAX
  imports DOMAINS-SYNTAX
  syntax Val ::= Id
               | "lambda" Id "." Exp  [binder]
  syntax Exp ::= Val
               | Exp Exp              [strict, left]
               | "(" Exp ")"          [bracket]
  syntax KVariable ::= Id
endmodule

module LAMBDA
  imports LAMBDA-SYNTAX
  imports DOMAINS
  imports SUBSTITUTION
  syntax KResult ::= Val

  rule (lambda X:Id . E:Exp) V:Val => E[V / X]
endmodule
