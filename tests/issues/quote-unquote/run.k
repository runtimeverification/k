load basic-run
load k-visitor
load quote-unquote

load ../ids
load exp
load if
load substitution
load lambda
load mu
load seq
load ref
load io
load while
load programs

kmod RUN is including QUOTE-UNQUOTE-PROGRAMS + BASIC-RUN 
  configuration <T><k> .K </k> <nextId>0</nextId> <mem>.Map</mem> <nextLoc>0</nextLoc><in>.List</in><out>.List</out></T>
endkm
