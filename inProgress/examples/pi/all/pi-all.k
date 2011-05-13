
load ../../../modules/k-visitor
load ../../../modules/substitution
load ../pi-syntax
load ../pi-programs
load pi-all-semantics

kmod PI-ALL is including PI-ALL-SEMANTICS + PI-PROGRAMS             
  op run : KLabel -> K
  macro run(KL:KLabel) = top(<T_> <k> KL(.List{K}) </k> <_/T>)
endkm
