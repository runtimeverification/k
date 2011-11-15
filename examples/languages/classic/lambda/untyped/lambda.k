require /modules/substitution

module LAMBDA
  imports SUBSTITUTION

  syntax Val ::= "lambda" Binding      [:prec 100 latex "\lambda{#1}":]
//reusing the binding syntax from the generic substitution
//Usual lambda-calculi '.' cannot be used because of the current K parser
  syntax Binding ::= "[" #Id "]" Exp [:ditto latex "{#1}.{#2}":]
  syntax Exp ::= #Id
               | Val
               | Exp Exp             [:strict:]

//@ making the tool understand that values are results
  syntax KResult ::= #Id | Val  

  configuration <k> $PGM:Exp </k> <nextId> 0 </nextId>

//@ $\beta$-substitution
  rule <k> (lambda[X:#Id] E:Exp) V:Val => E[V / X] ...</k>
end module
