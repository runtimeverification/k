in ../../../k-prelude
in exp-untyped-syntax
in ../exp-programs
in exp-untyped-semantics


kmod EXP-UNTYPED is including EXP-UNTYPED-SEMANTICS + EXP-PROGRAMS 
  op run : KLabel -> Bag 
  eq run(KL:KLabel) = run(KL,.List{K}) 
  op run : KLabel List{K} -> Bag 
  eq run(KL,L:List{K}) = <T_> <k> KL(L) </k> <_/T> 
endkm
