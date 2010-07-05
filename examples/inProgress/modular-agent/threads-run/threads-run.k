load ../basic-run
load ../exp
load ../imp
load ../threads

load ../ids
load ../../substitution/substitution
load ../fun
load ../control
load ../io
load ../ref
load threads-programs

kmod THREADS-RUN is including BASIC-RUN + THREADS-PROGRAMS
  configuration <T> 
                <thread*> 
                  <k> .K </k> <nextId> 0 </nextId> <holds> .Map </holds>
                </thread*>
                <in> .List </in> <out> .List </out>
                <mem> .Map </mem> <nextLoc> 0 </nextLoc>
                <busy> .Set </busy> </T>
endkm
