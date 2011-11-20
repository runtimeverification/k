require /modules/substitution

module LAMBDA-SYNTAX 

  syntax Exp ::= Val
               | Exp Exp                [:seqstrict gather(E e):]

  syntax Val ::= "lambda" #Id . Exp       [:prec 100 latex "\lambda{#1}.{#2}":]
               | #Id
end module

module LAMBDA imports LAMBDA-SYNTAX + SUBSTITUTION
 
 configuration <k> $PGM:Exp </k>
 syntax KResult ::= Val  

  context lambda[_] `[HOLE`]:Exp

//@ $\beta$-substitution
  rule <k> (lambda X:#Id.E:Exp) V:Val => E[V / X] ...</k>


  rule isBinder(lambda X.E) => true
end module
