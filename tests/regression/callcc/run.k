require /modules/basic-run
require /modules/k-visitor
require /modules/substitution
require /modules/lambda
require /modules/callcc

require ../ids
require /modules/exp
require /modules/if
require programs

kmod RUN is including BASIC-RUN + CALLCC-PROGRAMS 
  configuration <T> <k> .K </k> <nextId> 0 </nextId> </T>
endkm
