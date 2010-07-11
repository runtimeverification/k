load ../pi
load pi-all-semantics

kmod PI-ALL is including PI-ALL-SEMANTICS + PI-PROGRAMS             
  op run : KLabel -> Bag
  macro run(KL:KLabel) = <T_> <k> KL(.List{K}) </k> <_/T>
endkm
