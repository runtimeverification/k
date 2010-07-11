load ../pi
load pi-io-syntax
load pi-io-semantics
load pi-io-programs

kmod PI-IO is including PI + PI-IO-SEMANTICS + PI-IO-PROGRAMS
  op run : KLabel List{K} -> Bag
  macro run(KL:KLabel,L:List{K}) = <T> <sum> <k> KL(.List{K}) </k> </sum> <sum> <k> input(L) </k> </sum> <nextId> 0 </nextId> <out> .List </out> </T>
endkm

