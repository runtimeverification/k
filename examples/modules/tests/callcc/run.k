load ../basic-run
load ../../k-visitor
load ../../substitution
load ../../lambda
load ../../callcc

load ../ids
load ../../exp
load ../../if
load programs

kmod RUN is including BASIC-RUN + CALLCC-PROGRAMS 
  configuration <T> <k> .K </k> <nextId> 0 </nextId> </T>
endkm
