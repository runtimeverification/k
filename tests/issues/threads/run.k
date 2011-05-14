load basic-run
load seq
load threads

load ../ids
load exp
load if
load k-visitor
load substitution
load lambda
load halt
load io
load ref
load while
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
