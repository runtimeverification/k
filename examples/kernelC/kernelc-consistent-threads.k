kmod KERNELC-CONSISTENT-THREADS is including KERNELC-BASIC-SEMANTICS + KERNELC-CONSISTENT-MEMORY
  configuration <T ?> <threads> <thread*> <k> .K </k> <env> .Map </env> <id> 0 </id> </thread*> 
                    </threads> <locks> .Map </locks>  <cthreads> .Set </cthreads> @latex("\\\\\\")                     <funs> .Map </funs> <in> .List </in> <out> "" </out> 
                   <mem> .Map </mem> <ptr> .Map </ptr> 
                   <next> initialLoc </next> </T ?> 
                <result ?> "" </result ?>

  context 'spawn_('_`(_`)(_,,`[HOLE`]:K)) 
  rule <k> 'spawn_('_`(_`)(X:Id,,Vl:List{Val})) => N <_/k> <next> N:Nat => increment(N,1) </next> (. => <thread_> <k>'_`(_`)(X,,Vl)</k> <id> N </id> <_/thread>) 
  rule (<thread_> <k> V:Val </k> <id> N </id> <_/thread> => .) <cthreads_> . => SetItem(N) <_/cthreads> [structural]

  rule <k> join(N) => 0 <_/k> <cthreads_> SetItem(N) <_/cthreads> [structural]

  rule <k> acquire(N) => void <_/k> <id> N' </id> <locks_> N |-> (-1 => N':Nat) <_/locks>
  rule <k> release(N) => void <_/k> <id> N' </id> <locks_> N |-> (N' => -1) <_/locks>
  rule <k> acquire(N) => void <_/k> <id> N' </id> <locks> Locks:Map (. => N |-> N') </locks>
    if notBool(N in keys(Locks))
endkm
