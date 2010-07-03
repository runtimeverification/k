load ../../../../k-prelude
load ../../substitution/substitution
kmod SIMPLY-TYPED-SEMANTICS is including SUBSTITUTION
  syntax Type ::= type
                | Type --> Type [latex "{#1}\rightarrow{#2}"]
  syntax Exp ::= Val
               | ( )
               | lambda Type : BoundingExp [latex "\lambda_{{#1}}{#2}"]
               | Exp Exp [strict]
  syntax Val ::= Type
  syntax Builtins ::= Type
  syntax KResult ::= Val 
  syntax K ::= K ->> K [strict(2) latex "{#1}\twoheadrightarrow{#2}"]
  rule () => type
  rule (T:Type --> T':Type) T => T'
  rule <k> lambda T : (X:Id -> E:Exp) => T ->> E[T/X] <_/k>

  rule T ->> T' => T --> T' [structural]
endkm

kmod SIMPLY-TYPED-PROGRAMS is including SIMPLY-TYPED-SEMANTICS
  syntax Id ::= x | f
  syntax Exp ::= p1 | p2 | p3
  macro p1 = lambda type:(x-> lambda type-->type:(f-> (f x)))
  macro p2 = lambda type:(x-> (x x))
  macro p3 = lambda type : (x -> lambda (type --> (type --> (type --> type))) : (f -> ((f x) x)))
endkm

kmod SIMPLY-TYPED-LAMBDA is including SIMPLY-TYPED-PROGRAMS
  syntax Bag ::= run ( KLabel )
  macro run(L:KLabel) = <k>L(.List{K})</k> <nextId>0</nextId>
endkm
