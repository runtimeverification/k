kmod KERNELC-RELAXED-THREADS is including KERNELC-BASIC-SEMANTICS 

  configuration <T ?> <threads> <thread*> <k> .K </k> <env> .Map </env> <buffer> .List </buffer> <id> 0 </id> <blocked> false </blocked> </thread*> 
                    </threads> <cthreads> .Set </cthreads>
                    <funs> .Map </funs> <in> .List </in> <out> "" </out> 
                   <ptr> .Map </ptr> <mem> .Map </mem>
                   <locks> .Map </locks> <next> initialLoc </next> </T ?> 
                <result ?> "" </result ?>

  syntax ListItem ::= bwrite ( Nat , Val )
  syntax K ::= Bool

  context 'spawn_('_`(_`)(_,,`[HOLE`]:K)) 
  rule <k> 'spawn_('_`(_`)(X:Id,,Vl:List{Val})) => N <_/k> <next> N:Nat => increment(N,1) </next> <buffer> .List </buffer> (. => <thread_> <k>'_`(_`)(X,,Vl)</k> <id> N </id> <_/thread>) 
  rule (<thread_> <k> V:Val </k> <id> N </id> <buffer> .List </buffer> <_/thread> => .) <cthreads_> . => SetItem(N) <_/cthreads> [structural]

  rule <k> join(N) => 0 <_/k> <buffer> .List </buffer> <cthreads_> SetItem(N) <_/cthreads> [structural]

  rule <k> acquire(N) => void <_/k> <id> N' </id> <buffer> .List </buffer> <blocked> false </blocked> 
       <locks_> N |-> (-1 => N':Nat) <_/locks>
  rule <k> acquire(N)  <_/k> <blocked> false => true </blocked> <locks_> N |-> N2:Nat <_/locks>  
     [structural]
  rule <k> acquire(N)  <_/k>  <blocked> true => false </blocked> <locks_> N |-> -1 <_/locks>
     [structural]

  rule <k> release(N) => void <_/k> <id> N' </id> <buffer> .List </buffer> <locks_> N |-> (N' => -1) <_/locks>
  rule <k> acquire(N) => void <_/k> <id> N' </id> <buffer> .List </buffer> <locks> Locks:Map (. => N |-> N') </locks>
    if notBool(N in keys(Locks))

  rule <k> *N => V <_/k> <buffer_> bwrite(N, V) Mem:List </buffer> if notBool(N in locations(Mem)) [structural]
  rule <k> *N=V => V <_/k> <buffer_> .List => bwrite(N, V) <_/buffer> [structural]

  rule <k> *N => V <_/k> <buffer> Mem </buffer> <mem_> N |-> V <_/mem> if notBool(N in locations(Mem))
  rule <blocked> false </blocked> <buffer> bwrite(N, V) => . <_/buffer> <mem_> N |-> (_ => V) <_/mem>


  syntax Set ::= locations List
 
  rule locations(.List) => .Set [structural]
  rule locations(bwrite(N, V) Mem) => SetItem(N) locations(Mem) [structural]
endkm
