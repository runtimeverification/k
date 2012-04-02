
module SUBSTITUTION
  syntax List{K} ::= List{K} [ K /-/ Id ] [prec 0]
  syntax K ::= K [ K / Id ] [prec 0]
  syntax K ::= Id 
  
  define X[K/X] => K [structural]
  define KL:KLabel(L:List`{K`})[K:K/X:Id] => KL(L[K/-/X]) when KL(L) =/=K X [structural]
  define (K1:K ~> K2:K)[K/X] => (K1[K/X]) ~> (K2[K/X]) when K1 =/=K .K andBool K2 =/=K .K [structural]
  define (K1,,L)[K/-/X] => (K1[K/X]),,(L[K/-/X]) [structural]
  define .K[K/X] => .K [structural]
  define .List{K}[K/-/X] => .List{K} [structural]
end module

module SIMPLY-TYPED-SEMANTICS imports SUBSTITUTION
  syntax Type ::= type
                | Type --> Type [latex "{#1}\rightarrow{#2}"]
  syntax K ::= Id
             | lambda Id : Type . K [latex "\lambda{#1}\mathord{:}{#2}\mathrel{.}{#3}"]
             | K K
  syntax KResult ::= Type 

  rule (T:Type --> T':Type) T => T' [anywhere]
  rule lambda X:Id : T.E:K  => '_-->_(T,,E[T/X]) [anywhere]
end module

module SIMPLY-TYPED-PROGRAMS imports SIMPLY-TYPED-SEMANTICS
  syntax Id ::= x | f
  syntax K ::= p1 | p2 | p3 | p4
  macro p1 = lambda x:type. lambda f:(type-->type).(f x)
  macro p2 = lambda x:type.(x x)
  macro p3 = lambda x:type.lambda f:(type --> (type --> (type --> type))). ((f x) x)
  macro p4 = lambda x:type.f
end module

module SIMPLY-TYPED-LAMBDA imports SIMPLY-TYPED-PROGRAMS
  syntax K ::= run ( KLabel )
  macro run(L:KLabel) = L(.List{K})
end module
