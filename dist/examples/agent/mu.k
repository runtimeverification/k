require "lambda.k"

module MU-SYNTAX imports LAMBDA-SYNTAX
  syntax K ::= "mu" Id "." K [binder, latex("\mu{#1}.{#2}")]
endmodule

module MU 
  imports MU-SYNTAX 
  imports LAMBDA

//Fix point operator (through beta-substitution)
  rule (mu X:Id . E:K) => E[(mu X . E) / X] 
endmodule
