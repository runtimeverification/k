require /modules/substitution

module LAMBDA-SYNTAX
  imports SUBSTITUTION

  syntax Val ::= "lambda" Binding      [:prec 100 latex "\lambda{#1}":]
               | #Id

//reusing the binding syntax from the generic substitution
//Usual lambda-calculi '.' cannot be used because of the current K parser
  syntax Binding ::= "[" #Id "]" Exp [:prec 99 latex "{#1}.{#2}":]
  syntax Exp ::= Val
               | Exp Exp             [:strict:]
end module

module LAMBDA
  imports LAMBDA-SYNTAX
 
 configuration <k> $PGM:Exp </k> <nextId> 0 </nextId>

//@ making the tool understand that values are results
  syntax KResult ::= Val  


//@ $\beta$-substitution
  rule <k> (lambda[X:#Id] E:Exp) V:Val => E[V / X] ...</k>
end module
