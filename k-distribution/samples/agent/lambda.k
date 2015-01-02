// Copyright (c) 2012-2015 K Team. All Rights Reserved.
require "modules/substitution.k"
require "basic-exp.k"
require "id.k"
require "val.k"

module LAMBDA-SYNTAX
  imports BASIC-EXP-SYNTAX
  imports ID-EXP-SYNTAX
  syntax Lambda ::= "\\" Id "." Exp [lam, binder, latex(\lambda{#1}.{#2})]
  syntax Exp ::= Exp Exp [app, left, strict]
               | Lambda

  syntax priorities app > lam
endmodule

module LAMBDA
  imports LAMBDA-SYNTAX
  imports SUBSTITUTION
  imports VAL

  syntax Val ::= Id
               | Lambda

  syntax Variable ::= Id

// Function application (through beta-substitution)
  rule  (\ X:Id . E:K) V:KResult => E[V / X]
endmodule
