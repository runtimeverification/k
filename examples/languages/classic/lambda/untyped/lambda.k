require /modules/substitution

module LAMBDA-SYNTAX 

  syntax Exp ::= Val
               | Exp Exp            [:seqstrict gather(E e):]

  syntax Val ::= "lambda" #Id . Exp [:binder prec 100 latex "\lambda{#1}.{#2}":]
               | #Id
end module

module LAMBDA imports LAMBDA-SYNTAX + SUBSTITUTION
 
 configuration <k> $PGM:Exp </k>
 syntax KResult ::= Val  

//@ $\beta$-substitution
  rule <k> (lambda X:#Id.E:Exp) V:Val => E[V / X] ...</k>

end module
