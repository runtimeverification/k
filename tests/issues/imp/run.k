load basic-run
load seq
load if
load while

load ../ids
load exp
load k-visitor
load substitution
load lambda
load ref
load programs

kmod RUN is including IMP-PROGRAMS + BASIC-RUN
  configuration <T> <k> .K </k>  <nextId> 0 </nextId>
                <mem> .Map </mem> <nextLoc> 0 </nextLoc> </T>
endkm
