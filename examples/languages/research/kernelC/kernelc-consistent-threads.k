kmod KERNELC-CONSISTENT-THREADS is including KERNELC-THREADS-SYNTAX 
  including KERNELC-SEMANTICS + KERNELC-CONSISTENT-MEMORY
  /*@  \section{Basic semantics for threads}

    For executing multithreaded programs, the configuration must be updated to group computation, local variables and call stack in a {\sf thread} cell, which is identified by an {\sf id}.  Multiple threads are grouped in a {\sf threads} cell.  Additionally, the ids of all completed threads are gathered in the {\sf cthreads} cell.
  */

  configuration 
  <T multiplicity="?"> 
     <threads> <thread multiplicity="*"> 
       <k> .K </k> 
       <env> .Map </env>
       <fstack> .List </fstack>
        <id> 0 </id> 
     </thread> </threads>
     <locks> .Map </locks>  
     <cthreads> .Set </cthreads>       @latex("\\kBR")    
     <funs> .Map </funs>              
     <in> .List </in> 
     <out> "" </out> 
     <mem> .Map </mem> 
     <ptr> .Map </ptr> 
     <next> 1 </next> 
     <rand> 0 </rand>
  </T> 
  <result multiplicity="?"> "" </result>

  //@ \subsection{Locks} A lock is acquired if not already acquired by any thread.  Note that we don't model here re-entrant locks.
  rule <k> acquire(N:Nat) => void <_/k> <id> T:Nat </id> 
       <locks> Locks:Map (. => N |-> T) </locks>
    if notBool(N in keys(Locks))

  rule <k> release(N) => void <_/k> <id> T </id> 
       <locks_> N |-> T => . <_/locks>

  //@ \subsection{Spawn} The semantics of spawn is the one mentioned in the thread syntax.  We first have a context for evaluating the arguments of the function call (without callng the function, then we delegate the function call to a new thread.
  context 'spawn_('_`(_`)(_,,`[HOLE`]:K)) 
  rule <k> 'spawn_('_`(_`)(X:Id,,Vl:List{Val})) => T <_/k> 
       <next> T:Nat => T +Int 1 </next> 
       (. => <thread_> <k>'_`(_`)(X,,Vl)</k> <id> T </id> <_/thread>) 


  //@ \subsection{Thread end and join}  Upon completion a thread registers its {\sf id} in the set of completed threads, which is used as a signal to {\tt join}.
  rule (<thread_> <k> V:Val </k> <fstack> .List </fstack> <id> T </id> <_/thread> => .) 
       <cthreads_> . => SetItem(T) <_/cthreads> [structural]

  rule <k> join(T) => 0 <_/k> <cthreads_> SetItem(T) <_/cthreads> [structural]



endkm
