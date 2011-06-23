require /modules/basic-run
require /modules/seq
require /modules/threads

require ../ids
require /modules/exp
require /modules/if
require /modules/k-visitor
require /modules/substitution
require /modules/lambda
require /modules/halt
require /modules/io
require /modules/ref
require /modules/while
require programs

kmod RUN is including BASIC-RUN + THREADS-PROGRAMS
  configuration <T> 
                <thread multiplicity="*"> 
                  <k> .K </k> <nextId> 0 </nextId> <holds> .Map </holds>
                </thread>
                <in> .List </in> <out> .List </out>
                <mem> .Map </mem> <nextLoc> 0 </nextLoc>
                <busy> .Set </busy> </T>
endkm
