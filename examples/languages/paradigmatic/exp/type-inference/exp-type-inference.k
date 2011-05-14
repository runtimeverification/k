
in exp-type-inference-syntax
in ../exp-programs

in type-unification

in exp-type-inference-semantics


kmod EXP-TYPE-INFERENCE is including EXP-TYPE-INFERENCE-SEMANTICS + EXP-PROGRAMS 
  op solve : -> K 
  op run : KLabel -> Bag 
  eq run(KL:KLabel) = run(KL,.List{K}) 
  op run : KLabel List{K} -> Bag 
---- first step: accumulate the type constraints (also partially solving them when creating type schemas)
  eq run(KL,L:List`{K`}) = <T_> <k> KL(L) ~> solve </k> <_/T> 
--- second step: solve the remaining constraints and apply resulting substitution to the result type
  rule <k> T:Type ~> solve => Eqns:Set[T] </k> <eqns> <started> .Set </started> <solved> Eqns </solved> </eqns> 
endkm
