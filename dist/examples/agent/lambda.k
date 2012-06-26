require "modules/substitution.k"

module LAMBDA-SYNTAX
  syntax K ::= Id
             | "(" K ")" [bracket]
             | K K [left, strict]
             > "\\" Id "." K [binder, latex("\lambda{#1}.{#2}")]
endmodule

module LAMBDA 
  imports SUBSTITUTION
  imports LAMBDA-SYNTAX
  syntax KResult ::= Id 
                   > "\\" Id "." K [binder, latex("\lambda{#1}.{#2}")]

// Function application (through beta-substitution)
  rule  (\ X:Id . E:K) V:KResult => E[V / X] 
endmodule
