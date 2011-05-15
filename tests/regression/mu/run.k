in /modules/basic-run
in /modules/k-visitor
in /modules/substitution
in /modules/mu

load ../ids
in /modules/exp
in /modules/if
in /modules/lambda
load programs

kmod RUN is including BASIC-RUN + MU-PROGRAMS 
  configuration <T> <k> .K </k> <nextId> 0 </nextId> </T>
  syntax KResult ::= Id
endkm
