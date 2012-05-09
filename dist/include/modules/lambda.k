require "substitution.k"

module LAMBDA imports SUBSTITUTION
  syntax KResult ::= Id 
                   | "\" Id "." K   [binder, prec(100), latex("\lambda{#1}.{#2}")]
  syntax K ::= K K                [strict, left, prec(0), gather (E e)]

  //Function application (through beta-substitution)
  rule <k> (\ X:Id . E:K) V:KResult => E[V / X] ...</k>
endmodule
