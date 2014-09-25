// Copyright (c) 2012-2014 K Team. All Rights Reserved.
require "lambda.k"

module MU-SYNTAX imports LAMBDA-SYNTAX
  syntax Exp ::= "mu" Id "." Exp [mu, binder, latex(\mu{#1}.{#2})]
  syntax priorities app > mu
endmodule

module MU
  imports MU-SYNTAX
  imports LAMBDA

//Fix point operator (through beta-substitution)
  rule (mu X:Id . E:K) => E[(mu X . E) / X]
endmodule
