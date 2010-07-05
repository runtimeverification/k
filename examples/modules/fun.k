kmod FUN is including SUBSTITUTION
  syntax K ::= lambda Id . K [latex "\lambda{#1}.{#2}"]
             | K K  [strict]
             | mu Id . K [latex "\mu{#1}.{#2}"]

  syntax KResult ::= Id 
                   | aLambda K [latex "\lambda{#1}"]
  syntax K ::= aMu K [latex "\mu{#1}"]

  macro lambda X:Id . E:K = aLambda([X]E)
  macro mu X . E = aMu([X]E)
---Function application (through beta-substitution)
  rule <k> aLambda([X]E) E':K => E[E' / X]<_/k>

---Fix point operator (through beta-substitution)
  rule <k> aMu ([X]E) => E[aMu ([X]E) / X]<_/k>
endkm
