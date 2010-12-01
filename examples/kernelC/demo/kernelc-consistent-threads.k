kmod KERNELC-CONSISTENT-THREADS is including KERNELC-THREADS-SYNTAX 
  including KERNELC-SEMANTICS + KERNELC-CONSISTENT-MEMORY

  configuration 
  <T?> 
     <threads> <thread*> 
       <k> .K </k> 
       <env> .Map </env>
       <fstack> .List </fstack>
        <id> 0 </id> 
     </thread*> </threads>
     <locks> .Map </locks>  
     <cthreads> .Set </cthreads>       @latex("\\kBR")    
     <funs> .Map </funs>              
     <in> .List </in> 
     <out> "" </out> 
     <mem> .Map </mem> 
     <ptr> .Map </ptr> 
     <next> 1 </next> 
     <rand> 0 </rand>
  </T?> 
  <result?> "" </result?>

  rule <k> acquire(N:Nat) => void <_/k> <id> T:Nat </id> 
       <locks> Locks:Map (. => N |-> T) </locks>
    if notBool(N in keys(Locks))

  rule <k> release(N) => void <_/k> <id> T </id> 
       <locks_> N |-> T => . <_/locks>


  context 'spawn_('_`(_`)(_,,`[HOLE`]:K)) 
  rule <k> 'spawn_('_`(_`)(X:Id,,Vl:List{Val})) => T <_/k> 
       <next> T:Nat => T +Int 1 </next> 
       (. => <thread_> <k>'_`(_`)(X,,Vl)</k> <id> T </id> <_/thread>) 

  rule (<thread_> <k> V:Val </k> <fstack> .List </fstack> <id> T </id> <_/thread> => .) 
       <cthreads_> . => SetItem(T) <_/cthreads> [structural]

  rule <k> join(T) => 0 <_/k> <cthreads_> SetItem(T) <_/cthreads> [structural]



endkm
