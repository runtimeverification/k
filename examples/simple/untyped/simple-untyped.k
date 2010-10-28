in ../../../k-prelude
in simple-untyped-syntax
in simple-untyped-programs

kmod SIMPLE-UNTYPED-SEMANTICS is including SIMPLE-UNTYPED-DESUGARED-SYNTAX + K

-------------------------------------------------------------
--- Values that various fragments of programs evaluate to ---
-------------------------------------------------------------

  syntax Val ::= Int | Bool
               --- Array values are wrapped as specific reference values, where:
               --- 1st argument = the location of the first element in the array, and
               --- 2nd argument = the array size (array elements are contiguously allocated)
               | array ( Nat , Nat )
               --- Function values; like arrays, functions also evaluate to their address
               --- (wrapped as a specific "function" value) and the address contains
               --- the actual function body (as an untyped "lambda" value")
               | function( Nat )
               | lambda ( List{Id} , Stmt ) [latex "\lambda{#1}\,.\,{#2}"]

--- the values are expressions
  syntax Exp ::= Val


-------------------------------------
--- Computations "swallow" syntax ---
-------------------------------------

--- We have to subsort all the syntactic categories to K, and the lists of values
--- to KResult.  Recall that the second argument of a function application is a list
--- of expressions, so that becomes a result when it becomes a list of values
  syntax K ::= List{Exp} | Stmts           --- Grigore: check why we can remove List{Exp} from here
  syntax KResult ::= List{Val}


---------------------
--- Configuration ---
---------------------

  configuration <T> 
                     <k> K:K </k>
                     <fstack> .List </fstack>
                     <env> .Map </env>
                     <genv> .Map </genv>
                     <store> .Map </store>
                     <in> .List </in>
                     <out> .List </out>
                     <nextLoc> 0 </nextLoc>
                </T>


---------------------------------------
--- Declarations and initialization ---
---------------------------------------

--- Variable declaration
  rule <k> var X:Id; => . <_/k>
       <env> Env:Map => Env[L:Nat / X] </env>
       <store_> . => L |-> 0 <_/store>
       <nextLoc> L => sNat(L) </nextLoc> 

--- Array declaration
  context var X[[HOLE]];
  rule <k> var X[N:Nat]; => . <_/k>
       <env> Env => Env[L/X] </env>
       <store_> . => L |-> array(sNat L, N) <_/store>
       <nextLoc> L => sNat L +Nat N </nextLoc>

--- Function declaration
  rule <k> function F:Id(Xl) S:Stmt => . <_/k>
       <env> Env => Env[L/F] </env>
       <nextLoc> L => L +Nat 2 </nextLoc>
       <store_> . => L|->function(sNat L)  sNat(L)|->lambda(Xl,S) <_/store>

--- When we are done with the first pass (preprocessing), i.e., the computation
--- and genv are empty, call main() and initialize the global environment
  rule <k> . => main(); </k> <env> Env </env> <genv> . => Env </genv>


-------------------
--- Expressions ---
-------------------

--- Variable lookup
  rule <k> X => V:Val <_/k> <env_> X|->L <_/env> <store_> L|->V <_/store>

--- Variable increment
  rule <k> ++X => I:Int +Int 1 <_/k>
       <env_> X |-> L <_/env>
       <store_> L |-> (I => I +Int 1) <_/store>

--- Arithmetic operators
  rule I1:Int + I2:Int => I1 +Int I2
  rule _-_(I1,I2) => _-Int_(I1,I2)
  rule I1 * I2 => I1 *Int I2
  rule I1 / I2 => I1 /Int I2 if I2 =/=Bool 0
  rule I1 % I2 => I1 %Int I2 if I2 =/=Bool 0
  rule - I => -Int I
  rule I1 < I2 => I1 <Int I2
  rule I1 <= I2 => I1 <=Int I2
  rule I1 > I2 => I1 >Int I2
  rule I1 >= I2 => I1 >=Int I2
  rule V1:Val == V2:Val => V1 ==Bool V2
  rule V1 != V2 => V1 =/=Bool V2
  rule T1:Bool and T2:Bool => T1 andBool T2
  rule T1 or T2 => T1 orBool T2
  rule not(T:Bool) => notBool(T)

--- Array lookup.  Untyped SIMPLE does not check array bounds
--- We prefer to use a helper computation item, lookup, to avoid locking the store
  rule <k> array(L,_)[N] => lookup (L +Int N) <_/k> [structural]
  syntax K ::= lookup Nat
  rule <k> lookup L => V <_/k> <store_> L |-> V <_/store>

--- Size of array
  rule sizeOf(array(_,N)) => N

--- Function call. The environment and the computation are pushed onto the stack
  rule <k> _`(_`)(function(L),Vl:List{Val}) ~> K => S ~> return(0); </k>
       <fstack> . => (Env,K) <_/fstack>
       <env> Env => GEnv[N..N+Nat|Xl| / getList{K}(Xl)] </env>
       <genv> GEnv:Map </genv>
       <store_> L |-> lambda(Xl,S) (. => N..N+Nat|Xl| |-> getList{K}(Vl)) <_/store>
       <nextLoc> N => N +Nat |Xl| </nextLoc>
  rule <k> return(V:Val); ~> _ => V ~> K </k>
       <fstack> (Env,K) => . <_/fstack>
       <env> _ => Env </env>

--- Read
  rule <k> read() => I <_/k> <in> ListItem(I) => . <_/in>


------------------
--- Statements ---
------------------

--- Empty blocks. One can make the rule below structural, if one doesn't want it to count as step
  rule {} => .

--- Nonempty Blocks. Make sure the environment is recovered after the block executes
--- This rule can also be structural if one does not want entering a block to count as step
  rule <k> {Ss:Stmts} => Ss~>env(Env) <_/k> <env> Env </env>

--- Sequential composition.  Desugared into K's sequentialization.  Can also be structural
  rule S1:Stmt S2:Stmt => S1~>S2

--- Variable assignment
  rule <k> X=V; => . <_/k> <env_> X|->L <_/env> <store_> L|->(_=>V) <_/store>

--- Array assignment
--- We grab the whole store here, because we need to block it when writing a location
--- for the first time, to avoid conflicts with other threads that may also want to write it.
--- This happens because we deliberately decided NOT to allocate/initialize the array locations
--- when the array is created, to save time/computation.  Thus, the first write to a location acts
--- as "allocation" of that location.  To avoid such an aggressive locking of the store (which
--- inhibits true concurrency, since other threads may want to concurrently read/write other
--- locations), one would need to explicitly "allocate" all the array locations at declaration time
  context _[[HOLE]]=_;
  context [HOLE][_]=_;
  rule <k> array(L,_)[N] = V; => . <_/k> <store> Sigma:Map => Sigma[V/(L +Int N)] </store>

--- Expression statements.  They are only used for their side effects, so their result is descarded
  rule V; => .

--- Conditional
  rule if true then S else _ => S
  rule if false then _ else S => S

--- While loop unrolled only at the top of the computation (to avoid non-termination)
  rule <k> while B:Exp do S  => if B then {S while B do S} else {} <_/k>

--- Write
  rule <k> write(I); => . <_/k> <out_> . => ListItem(I) </out>


----------------------------------------------
--- Auxilliary declarations and operations ---
----------------------------------------------

--- Lists of values
  syntax List{Val} ::= Val | List{Val} , List{Val} [ditto]
  syntax List{Exp} ::= List{Val}

--- Length
  syntax Nat ::= `| List{Id} `| [latex "\mid\!\!{#1}\!\mid"]
  macro |.List{Id}| = 0  
  macro |X,Xl:List{Id}| = sNat |Xl|

--- Sequences of locations
  syntax List{K} ::= Nat .. Nat
  rule N1:Nat..N1 => .List{K} [structural]
  rule N1..N2:Nat => N1,,sNat N1..N2 [structural]

--- environment recovery
  syntax K ::= env ( Map )
  rule <k> env(Env) => . <_/k> <env> _ => Env </env> [structural]
  rule <k> V ~> (env(Env) => .) <_/k> <env> _ => Env </env> [structural]

--- the following is nedeed for stacking
  syntax ListItem ::=  ( Map , K )
endkm


-----------------------------------------
--- Main module, including everything ---
-----------------------------------------

kmod SIMPLE-UNTYPED is including SIMPLE-UNTYPED-SEMANTICS + SIMPLE-UNTYPED-PROGRAMS 
--- make sure the name of the final module is the capitalized version of the file name

  syntax Bag ::= run ( KLabel )

--- After loading simple-untyped-compiled into maude, type "rew run('program) .",
--- where 'program is the program you want to execute (among those in simple-untyped-programs.k)
  macro run(KL:KLabel)
        =
        <T_> 
           <k> KL(.List{K}) </k>
           <in>
              List(7,,23,,654,,656,,54,,456,,436345647643567,,354654364356,,4357643576)
           </in>
        <_/T> 
endkm
