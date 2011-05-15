in /modules/basic-run
in /modules/k-visitor
in /modules/substitution
in /modules/lambda

load ../ids
in /modules/exp
in /modules/if
load programs

kmod RUN is including BASIC-RUN + LAMBDA-PROGRAMS 
  configuration <T> <k> .K </k> <nextId> 0 </nextId> </T>
  syntax KResult ::= Id
endkm
