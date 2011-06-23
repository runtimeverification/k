require /modules/basic-run
require /modules/seq
require /modules/if
require /modules/while

require ../ids
require /modules/exp
require /modules/k-visitor
require /modules/substitution
require /modules/lambda
require /modules/ref
require programs

kmod RUN is including IMP-PROGRAMS + BASIC-RUN
  configuration <T> <k> .K </k>  <nextId> 0 </nextId>
                <mem> .Map </mem> <nextLoc> 0 </nextLoc> </T>
endkm
