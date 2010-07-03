load ../../../../k-prelude
load ../../substitution/substitution
kmod SIMPLY-TYPED-SEMANTICS is including SUBSTITUTION
  syntax Type ::= type
                | Type --> Type [hybrid strict latex "{#1}\rightarrow{#2}"]
  syntax K ::= Id
             | lambda Id : Type . K [latex "\lambda{#1}:{#2}.{#3}"]
             | K K [strict]
             | \lambda Type K [latex "{#1}\twoheadrightarrow{#2}"]
  syntax KResult ::= Type 

  macro lambda X : T.E = \lambda T ([X]E)

  rule (T:Type --> T':Type) T => T'
  rule <k> \lambda T ([X:Id]E:K) => '_-->_(T,,E[T/X]) <_/k>
endkm

kmod SIMPLY-TYPED-PROGRAMS is including SIMPLY-TYPED-SEMANTICS
  syntax Id ::= x | f
  syntax K ::= p1 | p2 | p3
  macro p1 = lambda x:type. lambda f:(type-->type).(f x)
  macro p2 = lambda x:type.(x x)
  macro p3 = lambda x:type.lambda f:(type --> (type --> (type --> type))). ((f x) x)
endkm

kmod SIMPLY-TYPED-LAMBDA is including SIMPLY-TYPED-PROGRAMS
  syntax Bag ::= run ( KLabel )
  macro run(L:KLabel) = <k>L(.List{K})</k> <nextId>0</nextId>
endkm
