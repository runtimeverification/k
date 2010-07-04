load ../basic-run
load ../exp
load ../imp
load ../threads

load ../ids
load ../../substitution/substitution
load ../fun
load ../io
load ../ref
load threads-programs

kmod THREADS-RUN is including BASIC-RUN + THREADS-PROGRAMS
  configuration <T> <threads> <thread*> 
                  <k> .K </k> <nextId> 0 </nextId> <holds> .Map </holds>
                </thread*> </threads>
                <in> .List </in> <out> .List </out>
                <mem> .Map </mem> <nextLoc> 0 </nextLoc>
                <busy> .Set </busy> </T>
endkm