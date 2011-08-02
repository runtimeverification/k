require substitution

module LAMBDA imports SUBSTITUTION
  syntax K ::= lambda #Id . K [latex "\lambda{#1}.{#2}"]
             | K K  [strict]

  syntax KResult ::= aLambda K [latex "\lambda{#1}"]

  macro lambda X:#Id . E:K = aLambda([X]E)
---Function application (through beta-substitution)
  rule <k> aLambda([X]E) E':KResult => E[E' / X]<_/k>
end module
