
load ../../substitution/substitution
kmod LAMBDA-CALL-BY-VALUE is including SUBSTITUTION
  syntax K ::= K K [strict]
             | lambda Id . K
  syntax KResult ::= \ K  | Id
  rule <k>(\([X]E))V:KResult=>E[V/X] <_/k>

  macro lambda X:Id . E:K = \([X]E)
endkm

