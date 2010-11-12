in ../../../k-prelude.maude
in fun-untyped-syntax
in ../fun-programs
in fun-untyped-semantics

kmod FUN-UNTYPED is including FUN-UNTYPED-SEMANTICS + FUN-PROGRAMS 
--- make sure the name of the final module is the capitalized version of the file name
  op run : KLabel -> Bag 
  eq run(KL:KLabel) = run(KL,.List{K}) 
  op run : KLabel List{K} -> Bag 
  eq run(KL,L:List`{K`}) = <T> <k> KL(L) </k> <env> .Map </env> <store> .Map </store> <nextLoc> 0 </nextLoc> </T> 
endkm
