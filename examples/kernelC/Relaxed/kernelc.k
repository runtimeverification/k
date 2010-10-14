load ../kernelc-syntax
load ../kernelc-basic-semantics
load kernelc-relaxed-threads
load ../Standard/standard-malloc-semantics
load ../kernelc-programs

kmod KERNELC is including STANDARD-MALLOC-SEMANTICS + KERNELC-PROGRAMS + KERNELC-RELAXED-THREADS 
  configuration <T ?> <threads> <thread*> <k> .K </k> <env> .Map </env> <buffer> .List </buffer> <id> 0 </id> <blocked> false </blocked> </thread*> 
                    </threads> <cthreads> .Set </cthreads>
                    <funs> .Map </funs> <in> .List </in> <out> "" </out> 
                   <ptr> .Map </ptr> <mem> .Map </mem>
                   <locks> .Map </locks> <next> initialLoc </next> </T ?> 
                <result ?> "" </result ?>

  rule <T_> <threads> .Bag </threads> <out> S:String </out> <_/T> => <result> S:String </result> 
    [structural]
endkm
