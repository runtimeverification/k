load ../basic-run
load ../../exp
load ../../imp

load ../ids
load ../../k-visitor
load ../../substitution
load ../../fun
load ../../ref
load programs

kmod RUN is including IMP-PROGRAMS + BASIC-RUN
  configuration <T> <k> .K </k>  <nextId> 0 </nextId>
                <mem> .Map </mem> <nextLoc> 0 </nextLoc> </T>
endkm
