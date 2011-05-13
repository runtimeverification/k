kmod KERNELC-THREADS-SYNTAX is including KERNELC-SYNTAX
  /*@ \section{Extending the syntax with threads}  
    The basic syntax of KERNELC is extended with some multi-threading primitives like thread creation, lock-synchronization, and thread-join.
    Since threas are not part of C we can afford more creativity here and we chose for spawn to be applied on the call of a function, with the intuition that the arguments of the function are evaluated in the current thread, then the function call is executed in a newly spawned thread.
  */
  syntax Exp ::= spawn Exp 
               | acquire ( Exp ) [strict] 
               | release ( Exp ) [strict] 
               | join ( Exp ) [strict]
endkm
