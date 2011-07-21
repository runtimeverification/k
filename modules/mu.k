require substitution

module MU imports SUBSTITUTION
  syntax K ::= mu Id . K [latex "\mu{#1}.{#2}"]
             | aMu K [latex "\mu{#1}"]

  macro mu X:Id . E:K = aMu([X]E)

---Fix point operator (through beta-substitution)
  rule <k> aMu ([X]E) => E[aMu ([X]E) / X]<_/k>
end module
