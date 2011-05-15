in /modules/basic-run
in /modules/seq
in /modules/threads

load ../ids
in /modules/exp
in /modules/if
in /modules/k-visitor
in /modules/substitution
in /modules/lambda
in /modules/halt
in /modules/io
in /modules/ref
in /modules/while
load programs

kmod RUN is including BASIC-RUN + THREADS-PROGRAMS
  configuration <T> 
                <thread multiplicity="*"> 
                  <k> .K </k> <nextId> 0 </nextId> <holds> .Map </holds>
                </thread>
                <in> .List </in> <out> .List </out>
                <mem> .Map </mem> <nextLoc> 0 </nextLoc>
                <busy> .Set </busy> </T>
endkm
