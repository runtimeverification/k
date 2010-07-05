load ../basic-run
load ../../k-visitor
load ../../substitution
load ../../fun

load ../ids
load ../../exp
load programs

kmod RUN is including BASIC-RUN + FUN-PROGRAMS 
  configuration <T> <k> .K </k> <nextId> 0 </nextId> </T>
endkm
