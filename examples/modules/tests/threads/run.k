load ../basic-run
load ../../threads

load ../ids
load ../../exp
load ../../k-visitor
load ../../substitution
load ../../fun
load ../../halt
load ../../io
load ../../ref
load ../../imp
load programs

kmod RUN is including BASIC-RUN + THREADS-PROGRAMS
  configuration <T> 
                <thread*> 
                  <k> .K </k> <nextId> 0 </nextId> <holds> .Map </holds>
                </thread*>
                <in> .List </in> <out> .List </out>
                <mem> .Map </mem> <nextLoc> 0 </nextLoc>
                <busy> .Set </busy> </T>
endkm
