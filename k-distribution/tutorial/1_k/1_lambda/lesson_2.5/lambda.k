// Copyright (c) 2013-2015 K Team. All Rights Reserved.
require "domains.k"
require "substitution.k"

module LAMBDA-SYNTAX
  imports DOMAINS-SYNTAX
  syntax Val ::= Id
               | "lambda" Id "." Exp  [binder]
  syntax Exp ::= Val
               | Exp Exp              [left]
               | "(" Exp ")"          [bracket]
  syntax KVariable ::= Id
endmodule

module LAMBDA
  imports LAMBDA-SYNTAX
  imports DOMAINS
  imports SUBSTITUTION
  rule (lambda X:Id . E:Exp) V:Val => E[V / X]   [anywhere]
endmodule
