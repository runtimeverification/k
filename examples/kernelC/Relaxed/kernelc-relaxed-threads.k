kmod KERNELC-RELAXED-THREADS is including KERNELC-BASIC-SEMANTICS

---(
Implementing a x86-TSO-like memory model inspired from the paper introducing x86-TSO (Scott Owens, Susmit Sarkar, Peter Sewell: A Better x86 Memory Model: x86-TSO. TPHOLs 2009: 391-407)

In reading the following natural language description taken verbatim from the paper, think about p as being a thread instead of a processor, and replace registers by local variables.  All synchronization operations (spawn, acquire, release, thread end, join) require the write buffer to be empty to proceed.  we have no meaning for ?FENCE ops.

1. p can read v from memory at address a if p is not blocked, has no buﬀered writes to a , and the 
memory does contain v at a ; 
2. p can read v from its write buﬀer for address a if p is not blocked and has v as the newest write to a in its buﬀer; 
3. p can read the stored value v from its register r at any time; 
4. p can write v to its write buﬀer for address a at any time; 
5. if p is not blocked, it can silently dequeue the oldest write from its write buﬀer to memory; 
6. p can write value v to one of its registers r at any time; 
7. if p’s write buﬀer is empty, it can execute an MFENCE (so an MFENCE cannot proceed until all writes have been dequeued, modelling buﬀer ﬂushing); LFENCE and SFENCE can occur at any time, making them no-ops; 
8. if the lock is not held, and p’s write buﬀer is empty, it can begin a LOCK’d instruction; and 
9. if p holds the lock, and its write buﬀer is empty, it can end a LOCK’d instruction. 
---) 

  configuration <T ?> <threads> <thread*> <k> .K </k> <env> .Map </env> <buffer> .List </buffer> <id> 0 </id> <blocked> false </blocked> </thread*> 
                    </threads> <cthreads> .Set </cthreads>
                    <funs> .Map </funs> <in> .List </in> <out> "" </out> 
                   <ptr> .Map </ptr> <mem> .Map </mem>
                   <locks> .Map </locks> <next> initialLoc </next> </T ?> 
                <result ?> "" </result ?>

  syntax ListItem ::= bwrite ( Nat , Val )
  syntax K ::= Bool

  context 'spawn_('_`(_`)(_,,`[HOLE`]:K)) 
  rule [spawn] : <k> 'spawn_('_`(_`)(X:Id,,Vl:List{Val})) => N <_/k> <next> N:Nat => increment(N,1) </next> <buffer> .List </buffer> (. => <thread_> <k>'_`(_`)(X,,Vl)</k> <id> N </id> <_/thread>) 
  rule (<thread_> <k> V:Val </k> <id> N </id> <buffer> .List </buffer> <_/thread> => .) <cthreads_> . => SetItem(N) <_/cthreads> [structural]

  rule <k> join(N) => 0 <_/k> <buffer> .List </buffer> <cthreads_> SetItem(N) <_/cthreads> [structural]

  rule <k> acquire(N)  <_/k> <blocked> false => true </blocked> <locks_> N |-> N2:Nat <_/locks>  
     [structural]
  rule <k> acquire(N)  <_/k>  <blocked> true => false </blocked> <locks_> Locks <_/locks>
    if notBool(N in keys(Locks))
     [structural]

  rule [release] : <k> release(N) => void <_/k> <id> N':Nat </id> <buffer> .List </buffer> <locks_> N |-> N' => .Map <_/locks>
  rule <k> acquire(N) => void <_/k> <id> N' </id> <buffer> .List </buffer> <locks> Locks:Map (. => N |-> N') </locks>
    if notBool(N in keys(Locks)) [label acquire]

  rule [local-deref] : <k> *N => V <_/k> <buffer_> bwrite(N, V) Mem:List </buffer> if notBool(N in locations(Mem))
  rule [local-inc] : <k> (*N)++ => I:Int <_/k> <buffer_> bwrite(N, I) Mem:List (. => bwrite(N, I +Int 1)) </buffer> if notBool(N in locations(Mem))
  rule <k> *N=V => V <_/k> <buffer_> .List => bwrite(N, V) </buffer> [structural]

  rule [global-deref]: <k> *N => V <_/k> <buffer> Mem </buffer> <mem_> N |-> V <_/mem> if notBool(N in locations(Mem))
  rule [global-inc]: <k> (*N)++ => I <_/k> <buffer> Mem (. => bwrite(N, I +Int 1))</buffer> <mem_> N |-> I <_/mem> if notBool(N in locations(Mem))
  rule [commit-write]: <blocked> false </blocked> <buffer> (bwrite(N, V) => .) <_/buffer> <mem_> N |-> (_ => V) <_/mem>
  


  syntax Set ::= locations List
 
  rule locations(.List) => .Set [structural]
  rule locations(bwrite(N, V) Mem) => SetItem(N) locations(Mem) [structural]
endkm
