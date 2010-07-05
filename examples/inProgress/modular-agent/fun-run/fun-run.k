load ../basic-run
load ../../reflection/reflection
load ../../substitution/substitution
load ../fun

load ../ids
load ../exp
load fun-programs

kmod FUN-RUN is including BASIC-RUN + FUN-PROGRAMS 
  configuration <T> <k> .K </k> <nextId> 0 </nextId> </T>
endkm
