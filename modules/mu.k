require lambda

module MU imports LAMBDA
  syntax K ::= "mu" #Id "." K [prec 100 latex "\mu{#1}.{#2}"]

---Fix point operator (through beta-substitution)
  rule <k> (mu X:#Id . E:K) => E[(mu X.E) / X] ...</k>

  rule isBinder(mu X.E) => true
end module
