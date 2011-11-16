require /modules/substitution

module LAMBDA-SYNTAX
  syntax Exp ::= Val
               | Exp Exp             [:strict gather(E e):]

  syntax Val ::= "lambda" Binding{Exp}      [:prec 100 latex "\lambda{#1}":]
               | #Id

/*@Our generic substitution uses a generic binding construct defined below 
to bind an id into an expression.  
To this generic binding one can associate different binders, such as 
`lambda' or `mu'.*/
  syntax Binding{Exp} ::= "[" #Id "]" Exp 
    [:prec 99 gather(e &) latex "{#1}.{#2}":]
//Usual lambda-calculi '.' cannot be used because of the current K parser;
//however, we transform the binding operator into "." when typesetting 
//the definition.
end module

module LAMBDA
  imports LAMBDA-SYNTAX
  imports SUBSTITUTION
 
/*@ Initial running configuration;  The <k> cell holds the program. 
 The <nextId> cell is required by the generic substitution for generating
fresh names. */
 configuration <k> $PGM:Exp </k> <nextId> 0 </nextId>

//@ making the tool understand that values are results
  syntax KResult ::= Val  


//@ $\beta$-substitution
  rule <k> (lambda[X:#Id] E:Exp) V:Val => E[V / X] ...</k>
end module
