in /modules/basic-run
in /modules/seq
in /modules/if
in /modules/while

load ../ids
in /modules/exp
in /modules/k-visitor
in /modules/substitution
in /modules/lambda
in /modules/ref
load programs

kmod RUN is including IMP-PROGRAMS + BASIC-RUN
  configuration <T> <k> .K </k>  <nextId> 0 </nextId>
                <mem> .Map </mem> <nextLoc> 0 </nextLoc> </T>
endkm
