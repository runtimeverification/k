load ../basic-run
load ../../substitution/substitution
load ../fun
load ../control

load ../ids
load ../exp
load control-programs

kmod CONTROL-RUN is including BASIC-RUN + CONTROL-PROGRAMS 
  configuration <T> <k> .K </k> <nextId> 0 </nextId> </T>
endkm
