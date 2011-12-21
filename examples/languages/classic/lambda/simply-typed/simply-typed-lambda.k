

kmod SUBSTITUTION is 
  syntax List{K} ::= List{K} [ K /-/ #Id ] [prec 0]
  syntax K ::= K [ K / #Id ] [prec 0]
  syntax K ::= #Id 
  
  rule X[K/X] => K [structural]
  rule KL:KLabel(L:List`{K`})[K:K/X:#Id] => KL(L[K/-/X]) when KL(L) =/=Bool X [structural]
  rule (K1:K ~> K2:K)[K/X] => (K1[K/X]) ~> (K2[K/X]) when K1 =/=Bool .K andBool K2 =/=Bool .K [structural]
  rule (K1,,L)[K/-/X] => (K1[K/X]),,(L[K/-/X]) [structural]
  rule .K[K/X] => .K [structural]
  rule .List{K}[K/-/X] => .List{K} [structural]
  
   
endkm

kmod SIMPLY-TYPED-SEMANTICS is including SUBSTITUTION
  syntax Type ::= type
                | Type --> Type [latex "{#1}\rightarrow{#2}"]
  syntax K ::= #Id
             | lambda #Id : Type . K [latex "\lambda{#1}\mathord{:}{#2}\mathrel{.}{#3}"]
             | K K
  syntax KResult ::= Type 

  rule (T:Type --> T':Type) T => T'
  rule lambda X:#Id : T.E:K  => '_-->_(T,,E[T/X])
endkm

kmod SIMPLY-TYPED-PROGRAMS is including SIMPLY-TYPED-SEMANTICS
  syntax #Id ::= x | f
  syntax K ::= p1 | p2 | p3 | p4
  macro p1 = lambda x:type. lambda f:(type-->type).(f x)
  macro p2 = lambda x:type.(x x)
  macro p3 = lambda x:type.lambda f:(type --> (type --> (type --> type))). ((f x) x)
  macro p4 = lambda x:type.f
endkm

kmod SIMPLY-TYPED-LAMBDA is including SIMPLY-TYPED-PROGRAMS
  syntax K ::= run ( KLabel )
  macro run(L:KLabel) = L(.List{K})
endkm
