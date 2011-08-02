
load kernelc-syntax
load kernelc-semantics
load kernelc-threads-syntax
load kernelc-relaxed-threads

kmod KERNELC-RELAXED is including  KERNELC-RELAXED-THREADS 
---running a program identified by its name, maybe with an input list
  syntax Bag ::= run ( KLabel ) 
               | run ( KLabel , List{K} )
  rule run ( L:KLabel ) => run(L,.List{K}) [structural]
--- Update the initial configuration by loading it in the <k> cell and then calling main.  Put the list of inputs in the <in> cell.
  rule run ( L, Il:List{K} ) 
    => <T_> <k> L(.List{K}) ~> '_`(`)(main) </k> <in> List(Il) </in> <_/T>    
  [structural]  

---Rule for extracting the output once all threads have finished
  rule <T_> <threads> .Bag </threads> <out> S:#String </out> <_/T> 
    => <result> S </result> [structural]

endkm
