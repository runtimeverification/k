
load ../../substitution/substitution
kmod LAMBDA-CALL-BY-NAME is including SUBSTITUTION
  syntax Exp ::= Val 
               | Exp Exp [strict(1)]
  syntax Val ::= lambda BoundingExp | Id
  syntax KResult ::= Val
  rule <k>(lambda(X:Id->E:Exp))V:Val=>E[V/X] <_/k>
endkm

