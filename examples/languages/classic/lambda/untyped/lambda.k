require /modules/substitution

module LAMBDA-SYNTAX imports BINDING

  syntax Exp ::= Val
               | Exp Exp                [:strict gather(E e):]

  syntax Val ::= "lambda" Binding       [:prec 100 latex "\lambda{#1}":]
               | #Id

  syntax Binding ::= "[" #Id "]" Exp    [:ditto:]
//Usual lambda-calculi '.' cannot currently be used for parsing issues.
//however, the binding operator is transformed into "." when typesetting.
end module

module LAMBDA imports LAMBDA-SYNTAX + SUBSTITUTION
 
/*@ Initial running configuration;  The <k> cell holds the program. 
 The <nextId> cell is required by the generic substitution for generating
fresh names. */
 configuration <k> $PGM:Exp </k> <nextId> 0 </nextId>

//@ making the tool understand that values are results
  syntax KResult ::= Val  


//@ $\beta$-substitution
  rule <k> (lambda[X:#Id] E:Exp) V:Val => E[V / X] ...</k>
end module
