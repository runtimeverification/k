load ../basic-run
load ../../halt

load ../ids
load ../../exp
load ../../k-visitor
load ../../substitution
load ../../lambda
load ../../mu
load programs

kmod RUN is including BASIC-RUN + HALT-PROGRAMS 
  configuration <T> <k> .K </k> <nextId> 0 </nextId> </T>
endkm
