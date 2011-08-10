load kernelc-syntax
load kernelc-semantics
load kernelc-threads-syntax
load kernelc-consistent-threads
load kernelc-programs
kmod KERNELC is including KERNELC-SYNTAX + KERNELC-SIMPLE-MALLOC + KERNELC-CONSISTENT-THREADS + KERNELC-PROGRAMS
//@\section{Putting everything together}

//@ Running a program identified by its name, maybe with an input list
  syntax Bag ::= run ( KLabel ) 
               | run ( KLabel , List{K} )
  rule run ( L:KLabel ) => run(L,.List{K})

/*@ Update the initial configuration by loading it in the {\sf k} cell 
and then calling main.  Put the list of inputs in the {\sf in} cell. */

  rule run ( L, Il:List{K} ) 
    => <T_> <k> L(.List{K}) ~> '_`(`)(main) </k> <in> List(Il) </in> <_/T>    

//@ Rule for extracting the output once all threads have completed

  rule <T_> <threads> .Bag </threads> <out> S:#String </out> <_/T> 
    => <result> S </result>

endkm
