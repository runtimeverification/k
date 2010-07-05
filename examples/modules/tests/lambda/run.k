load ../basic-run
load ../../k-visitor
load ../../substitution
load ../../lambda

load ../ids
load ../../exp
load programs

kmod RUN is including BASIC-RUN + LAMBDA-PROGRAMS 
  configuration <T> <k> .K </k> <nextId> 0 </nextId> </T>
  syntax KResult ::= Id
endkm
