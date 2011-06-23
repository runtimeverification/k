require /modules/basic-run
require /modules/halt

require ../ids
require /modules/exp
require /modules/if
require /modules/k-visitor
require /modules/substitution
require /modules/lambda
require /modules/mu
require programs

kmod RUN is including BASIC-RUN + HALT-PROGRAMS 
  configuration <T> <k> .K </k> <nextId> 0 </nextId> </T>
endkm
