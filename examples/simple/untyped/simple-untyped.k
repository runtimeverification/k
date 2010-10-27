in ../../../k-prelude
in simple-untyped-syntax
in simple-untyped-programs

kmod SIMPLE-UNTYPED-SEMANTICS is including SIMPLE-UNTYPED-DESUGARED-SYNTAX + K

-------------------------------------------------------------
--- Values that various fragments of programs evaluate to ---
-------------------------------------------------------------

  syntax Val ::= Int | Bool
               | array ( Nat , Nat )
                 --- array values are wrapped as specific values
               | function( Nat ) | lambda ( List{Id} , Stmt )
                 --- function values; like arrays, functions also evaluate to
                 ---   their address (wrapped as a specific "function" value) and the
                 ---   address contains the actual function body (as a "lambda" value")

--- the values are expressions
  syntax Exp ::= Val


-------------------------------------
--- Computations "swallow" syntax ---
-------------------------------------

--- We have to subsort all the syntactic categories to K, and the lists of values
--- to KResult.  Recall that the second argument of a function application is a list
--- of expressions, so that becomes a result when it becomes a list of values
  syntax K ::= Stmts
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


--------------------
--- Declarations ---
--------------------

--- Variable declaration
  rule <k> var X:Id; => .K <_/k>
       <env> Env:Map => Env[L:Nat / X] </env>
       <store_> .Map => L |-> 0 <_/store>
       <nextLoc> L => sNat(L) </nextLoc> 

--- Array declaration
  context var X[[HOLE]];
  rule <k> var X[N:Nat]; => . <_/k> 
       <env> Env => Env[L/X] </env>
       <store_>. => L |-> array(sNat L, N) <_/store>
       <nextLoc> L => sNat L +Nat N </nextLoc> 
  rule (sizeOf(array(_,N)) => N)   

--- Function declaration
  rule <k> function F:Id(Xl) S:Stmt => . <_/k> 
       <env> Env => Env[L/F] </env> 
       <nextLoc> L => L +Nat 2 </nextLoc> 
       <store_>(.Map => L |-> function(sNat L) sNat(L) |-> lambda(Xl,S))<_/store>

--- When we are done with the first pass (preprocessing), i.e., the computation and genv are empty,
---   call main and initialize the global environment
  rule <k> . => main(); </k> <env> Env </env> <genv> . => Env </genv>


-------------------
--- Expressions ---
-------------------

--- Variable lookup
  rule <k> X => V:Val <_/k>
       <env_> X |-> L <_/env>
       <store_> L |-> V <_/store>

--- Arithmetic expressions
  rule <k> ++X => I:Int +Int 1 <_/k>
       <env_> X |-> L <_/env>
       <store_> L |-> (I => I +Int 1) <_/store>
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

--- Array lookup
---    first arg. is the location of the first element in the array, and 
---    the second argument is the array size (= the index)
  rule <k> array(L,_)[N:Nat] => Sigma(L +Int N) <_/k> <store> Sigma:Map </store> .
                                --- untyped SIMPLE does not check array bounds

--- Read
  rule <k> read() => I <_/k> <in> ListItem(I) => . <_/in>

--- Function call ---
--- the environment and the computation are pushed in the stack at each function call
  rule <k> _`(_`)(function(L),Vl:List{Val})~>K:K => S~>return(0); </k> 
       <fstack> .List => (Env,K) <_/fstack>
       <env> Env => GEnv[N..N+Nat|Xl| / getList{K}(Xl)] </env>
       <genv> GEnv:Map </genv>
       <store_> L |-> lambda(Xl,S) (. => N..N+Nat|Xl| |-> getList{K}(Vl)) <_/store>
       <nextLoc> N => N +Nat |Xl| </nextLoc>
  rule <k> return(V:Val); ~> _ => V ~> K </k>
       <fstack> (Env:Map,K) => . <_/fstack>
       <env> _ => Env </env>


------------------
--- Statements ---
------------------

  rule {} => .
  rule <k> {Ss:Stmts} => Ss~>env(Env) <_/k> <env> Env:Map </env> 
  rule S1:Stmt S2:Stmt => S1~>S2 
  rule <k> X:Id = V:Val; => . <_/k> <env_> X|->L <_/env> <store_> L:Nat |->(_=>V) <_/store> 

--- Array assignment
  context _[[HOLE]]=_;
  context [HOLE][_]=_;
  rule <k> array(L,_)[N:Nat] = V; => . <_/k>
       <store> Sigma => Sigma[V/(L +Int N)] </store> 

  rule V; => .
  rule if true then S else _ => S
  rule if false then _ else S => S
  rule <k> while B:Exp do S  => if B then {S while B do S} else {} <_/k>
  rule <k> write(I:Int); => . <_/k> <out_> . => ListItem(I) </out>


----------------------------------------------
--- Auxilliary declarations and operations ---
----------------------------------------------

--- List{Val}
  syntax List{Val} ::= Val | List{Val} , List{Val} [ditto]
  syntax List{Exp} ::= List{Val}

--- length
  syntax Nat ::= `| List{Id} `|
  macro |.List{Id}| = 0  
  macro |X:Id,Xl:List{Id}| = sNat |Xl|

--- generate sequence of locations
  syntax List{K} ::= Nat .. Nat
  rule N1:Nat..N1 => .List{K} [structural]
  rule N1..N2:Nat => N1,,sNat N1..N2 [structural]

--- environment recovery
  syntax K ::= env ( Map ) 
  rule env(_) ~> env(Env:Map) => env(Env) [structural] 
  rule <k> env(Env) => . <_/k> <env> _ => Env </env> [structural] 
  rule <k> V:Val ~> (env(Env) => .) <_/k> <env> _ => Env </env> [structural]

--- the following is nedeed for stacking
  syntax ListItem ::=  ( Map , K )

endkm


-------------------
--- Main module ---
-------------------

kmod SIMPLE-UNTYPED is including SIMPLE-UNTYPED-SEMANTICS + SIMPLE-UNTYPED-PROGRAMS 
--- make sure the name of the final module is the capitalized version of the file name

  syntax Bag ::= run ( KLabel )

--- After loading simple-untyped-compiled into maude, type "rew run('program) .",
--- where 'program is the program you want to execute (among those in simple-untyped-programs.k)
  macro run(K:KLabel)
        =
        <T_> 
           <k> K(.List{K}) </k>
           <in>
              List(7,,23,,654,,656,,54,,456,,436345647643567,,
                   354654364356,,4357643576)
           </in>
        <_/T> 
endkm
