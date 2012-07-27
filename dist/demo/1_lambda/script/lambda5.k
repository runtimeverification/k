require "modules/substitution.k"

module LAMBDA
  imports SUBSTITUTION

  syntax Val ::= Id
               | "lambda" Id "." Exp  [binder, latex("\lambda{#1}.{#2}")]
  syntax Exp ::= Val
               | Exp Exp              [left]
               | "(" Exp ")"          [bracket]
  syntax KResult ::= Val

  context HOLE _
  context _ HOLE
  
  rule (lambda X:Id . E:Exp) V:Val => E[V / X]
endmodule
