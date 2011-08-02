require /modules/basic-run
require /modules/k-visitor
require /modules/substitution
require /modules/mu

require ../ids
require /modules/exp
require /modules/if
require /modules/lambda
require programs

kmod RUN is including BASIC-RUN + MU-PROGRAMS 
  configuration <T> <k> .K </k> <nextId> 0 </nextId> </T>
  syntax KResult ::= #Id
endkm
