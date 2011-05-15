in /modules/basic-run
in /modules/halt

load ../ids
in /modules/exp
in /modules/if
in /modules/k-visitor
in /modules/substitution
in /modules/lambda
in /modules/mu
load programs

kmod RUN is including BASIC-RUN + HALT-PROGRAMS 
  configuration <T> <k> .K </k> <nextId> 0 </nextId> </T>
endkm
