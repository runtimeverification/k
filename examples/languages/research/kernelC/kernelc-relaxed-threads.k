kmod KERNELC-RELAXED-THREADS is 
  including KERNELC-SEMANTICS + KERNELC-THREADS-SYNTAX

/*@  \section{A relaxed memory model}

Implementing a x86-TSO-like memory model inspired from the paper introducing x86-TSO:
\begin{quote}
 Scott Owens, Susmit Sarkar, Peter Sewell: \href{http://dx.doi.org/10.1007/978-3-642-03359-9_27}{A Better x86 Memory Model: x86-TSO}.
 22nd International Conference on Theorem Proving in Higher Order Logics (TPHOL'09) 391--407. 2009.
\end{quote}

In reading the following natural language description taken verbatim from the paper, think about p as being a thread instead of a processor, and replace registers by local variables.  All synchronization operations (spawn, acquire, release, thread end, join) act like an MFENCE operation by requiring the write buffer to be empty to proceed.

\begin{itemize}
\item $p$ can read $v$ from memory at address $a$ if $p$ is not blocked, has no buffered writes to $a$, and the 
memory does contain $v$ at $a$; 
\item $p$ can read $v$ from its write buffer for address $a$ if $p$ is not blocked and has $v$ as the newest write to $a$ in its buffer; 
\item $p$ can read the stored value $v$ from its register $r$ at any time; 
\item $p$ can write $v$ to its write buffer for address $a$ at any time; 
\item if $p$ is not blocked, it can silently dequeue the oldest write from its write buffer to memory; 
\item $p$ can write value $v$ to one of its registers $r$ at any time; 
\item if $p$'s write buffer is empty, it can execute an MFENCE (so an MFENCE cannot proceed until all writes have been dequeued, modelling buffer flushing); LFENCE and SFENCE can occur at any time, making them no-ops; 
\item if the lock is not held, and $p$'s write buffer is empty, it can begin a LOCK'd instruction; and 
\item if $p$ holds the lock, and its write buffer is empty, it can end a LOCK'd instruction. 
\end{itemize}

*/


/*@
\subsection{Rule 1} $p$ can read $v$ from memory at address $a$ if $p$ is not blocked, has no buffered writes to $a$, and the 
memory does contain $v$ at $a$; 
*/
  rule [global-deref]: <k> *N => V <_/k> <buffer> Mem </buffer> 
      <mem_> N:#Nat |-> V <_/mem> 
    if notBool(N in locations(Mem))


//@\subsection{Rule 2} $p$ can read $v$ from its write buffer for address $a$ if $p$ is not blocked and has $v$ as the newest write to $a$ in its buffer; 

  rule [local-deref] : <k> *N => V <_/k> 
       <buffer_> bwrite(N, V) Mem:List </buffer> 
    if notBool(N in locations(Mem))

//@\subsection{Rule 3} $p$ can read the stored value $v$ from its register $r$ at any time; this stays as in the original \KERNELC definition.



//@\subsection{Rule 4} $p$ can write $v$ to its write buffer for address $a$ at any time; 

  rule [buffer-write] : <k> *N = V => V <_/k> 
       <buffer_> .List => bwrite(N, V) </buffer> 
    [structural]

//@\subsection{Rule 5} if $p$ is not blocked, it can silently dequeue the oldest write from its write buffer to memory; 

  rule [commit-write]: <blocked> false </blocked> <buffer> 
       (bwrite(N, V) => .) <_/buffer> <mem_> N |-> (_ => V) <_/mem>

//@\subsection{Rule 6} $p$ can write value $v$ to one of its registers $r$ at any time; this stays as in the original \KERNELC definition.


//@\subsection{Rule 7} if $p$'s write buffer is empty, it can execute an MFENCE (so an MFENCE cannot proceed until all writes have been dequeued, modelling buffer flushing); LFENCE and SFENCE can occur at any time, making them no-ops; 


//@\subsection{Rule 8} if the lock is not held, and $p$'s write buffer is empty, it can begin a LOCK'd instruction;


  rule [acquire] : <k> acquire(N) => void <_/k> <id> T </id> 
        <buffer> .List </buffer> <locks> Locks:Map (. => N |-> T) </locks>
    if notBool(N in keys(Locks))

//@\subsection{Rule 9} if $p$ holds the lock, and its write buffer is empty, it can end a LOCK'd instruction. 

  rule [release] : <k> release(N) => void <_/k> <id> T:#Nat </id> 
       <buffer> .List </buffer> <locks_> N |-> T => .Map <_/locks>


//@\subsection{Initial configuration}  adds to \KERNELC's configuration a buffer for writes and a cell to maintain info whether a thread is blocked.

  configuration 
  <T multiplicity="?"> 
     <threads> <thread multiplicity="*"> 
       <k> .K </k> 
       <env> .Map </env>
       <fstack> .List </fstack>
       <buffer> .List </buffer>     --- This is to buffer writes
       <blocked> false </blocked>   --- Is thread blocked?
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
  </T> 
  <result multiplicity="?"> "" </result>

  //@ Structural rules for maintaining the status of the blocked cell
  rule <k> acquire(N)  <_/k> <blocked> false => true </blocked> 
       <locks_> N |-> T:#Nat <_/locks>       [structural]
  rule <k> acquire(N)  <_/k>  <blocked> true => false </blocked> 
       <locks_> Locks <_/locks>
    if notBool(N in keys(Locks))       [structural]


  //@\subsection{Thread semantics} changes because now all synchronization constrcts are assumed to generate an MFENCE instruction, and thus need to ensure the buffer is empty.

  context 'spawn_('_`(_`)(_,,`[HOLE`]:K)) 
  rule [spawn] : <k> 'spawn_('_`(_`)(X:#Id,,Vl:List{Val})) => T <_/k> 
                 <next> T:#Nat => T +Int 1 </next> 
                 <buffer> .List </buffer> 
                 (. => <thread_> <k>'_`(_`)(X,,Vl)</k> <id> T </id> <_/thread>) 
  rule (<thread_> <k> V:Val </k> <id> T </id> 
           <buffer> .List </buffer> 
        <_/thread> => .)   <cthreads_> . => SetItem(T) <_/cthreads> [structural]

  rule <k> join(N) => 0 <_/k>   <buffer> .List </buffer> 
       <cthreads_> SetItem(N) <_/cthreads> [structural]

  rule [local-inc] : <k> (*N)++ => I:#Int <_/k> 
       <buffer_> bwrite(N, I) Mem:List (. => bwrite(N, I +Int 1)) </buffer> 
    if notBool(N in locations(Mem))

  rule [global-inc]: <k> (*N)++ => I <_/k> 
       <buffer> Mem (. => bwrite(N, I +Int 1))</buffer> <mem_> N |-> I <_/mem> 
    if notBool(N in locations(Mem))

 //@ Auxilliary helping semantic constructs

  syntax ListItem ::= bwrite ( #Nat , Val )

  syntax Set ::= locations List
 
  rule locations(.List) => .Set [structural]
  rule locations(bwrite(N, V) Mem) => SetItem(N) locations(Mem) [structural]
endkm
