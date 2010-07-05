load ../basic-run
load ../../k-visitor
load ../../substitution
load ../../mu

load ../ids
load ../../exp
load ../../if
load ../../lambda
load programs

kmod RUN is including BASIC-RUN + MU-PROGRAMS 
  configuration <T> <k> .K </k> <nextId> 0 </nextId> </T>
  syntax KResult ::= Id
endkm
