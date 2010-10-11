load ../kernelc-syntax
load ../basic-kernelc-semantics
load standard-malloc-semantics
load ../kernelc-programs
load ../kernelc-race-detection
load ../instrument-program.k

kmod KERNELC is including STANDARD-MALLOC-SEMANTICS + KERNELC-PROGRAMS + KERNELC-RACE-DETECTION + INSTRUMENT-PROGRAM
  configuration <T> <threads> <thread*> 
                 < k ? > .K </ k ? > < race ? > .K </ race ? > 
                 <env> .Map </env> <id> 0 </id>
                  <event> false </event>  </thread*> 
                    </threads>  <cthreads> .Set </cthreads>
                    <funs> .Map </funs> <in> .List </in> <out> "" </out> 
                   <mem> .Map </mem> <ptr> .Map </ptr> 
                   <locks> .Map </locks> <next> initialLoc </next> 
                <trace> .List </trace> 
                </T> 
                <result> "" </result>

  rule <T_> <threads> .Bag </threads> <out> S:String </out> <trace> L:List </trace> <_/T> => <T>  <out> S:String </out> <trace> L:List </trace> </T> [structural]
endkm
