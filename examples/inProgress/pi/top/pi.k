load ../../../../k-prelude
load ../../../modules/k-visitor
load ../../../modules/substitution
load pi-syntax
load pi-semantics
load pi-programs

kmod PI is including PI-SEMANTICS + PI-PROGRAMS             
  op run : KLabel -> Bag
  macro run(KL:KLabel) = <T_> <k> KL(.List{K}) </k> <_/T>
endkm