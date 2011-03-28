---------------------------------------
--- SIMPLE-UNTYPED-SEMANTICS module ---
---------------------------------------

kmod SIMPLE-UNTYPED-SEMANTICS is including SIMPLE-UNTYPED-DESUGARED-SYNTAX + K

-------------------------------------------------------------
/*@ \subsubsection*{Values} that various fragments of programs evaluate to */
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
/*@ \subsubsection*{Computations} "swallow" syntax */
-------------------------------------

--- We have to subsort all the syntactic categories to K, and the lists of values
--- to KResult.  Recall that the second argument of a function application is a list
--- of expressions, so that becomes a result when it becomes a list of values
  syntax K ::= List{Exp} | Stmts           --- Grigore: check why we can remove List{Exp} from here
  syntax KResult ::= List{Val}


---------------------
/*@ \subsection*{Configuration}  */
---------------------

  configuration <T color="red">
                  <threads color="orange">
                    <thread multiplicity="*" color="yellow">
                      <k color="green"> K:K </k>
                      <fstack color="blue"> .List </fstack>
                      <xstack color="purple"> .List </xstack>
                      <env color="violet"> .Map </env>
                      <holds color="black"> .Map </holds>
                    </thread>
                  </threads>
                  <genv color="pink"> .Map </genv>
                  <store color="white"> .Map </store>
                  <busy color="cyan">.Set</busy>
                  <in color="magenta"> .List </in>
                  <out color="brown"> .List </out>
                  <nextLoc color="gray"> 0 </nextLoc>
                </T>


---------------------------------------
//@ \section*{Declarations and initialization} 
---------------------------------------

//@ \subsection*{Variable declaration}
  context var X = [HOLE];
  rule <k> var X:Id = V; => . <_/k>
       <env> Env:Map => Env[L:Nat/X] </env>
       <store_> . => L|->V <_/store>
       <nextLoc> L => sNat(L) </nextLoc> 

//@ \subsection*{Array declaration}
  context var X[_,`[HOLE`]:Exp,_];
  rule <k> var X[N:Nat]; => . <_/k>
       <env> Env => Env[L/X] </env>
       <store_> . => (L |-> array(sNat L, N)) sNat L..sNat L+Nat N |-> 0 <_/store>
       <nextLoc> L => sNat L +Nat N </nextLoc>


/*@ The rule below lazily handles multi-dimensional arrays through code generation.  The reason for handling it here than as a syntactic desugaring is that we want to ensure the dimensions of the array are already evaluated before we generate the code, to avoid strange behaviors for code like var a[++x,++x]; 
*/
  syntax Id ::= freshId ( Nat )
  rule <k> var X[N,N':Nat,Vl]; => 
           __((var (X[N]);), 
           for freshId(L) = 0 to N +Int -1 do {
             (var freshId(L +Nat 1)[N',Vl];)
             X[freshId(L)] = freshId(L +Nat 1); 
           }) <_/k>  <nextLoc> L => L +Nat 2 </nextLoc>  

//@ \subsection*{Function declaration}
  rule <k> function F:Id(Xl:List{Id}) S:Stmt => . <_/k>
       <env> Env => Env[L/F] </env>
       <nextLoc> L => L +Nat 2 </nextLoc>
       <store_> . => L|->function(sNat L)  sNat(L)|->lambda(Xl,S) <_/store>

/*@
 When we are done with the first pass (preprocessing), i.e., the computation
 contains only the token "execute" (see simple-untyped.k)
 and genv is empty, call main() and initialize the global environment
*/
  syntax K ::= execute
  rule <k> execute => main(); </k> <env> Env </env> <genv> . => Env </genv>


-------------------
//@ \section*{Expressions}
-------------------

//@ \subsection*{Variable lookup}
  rule <k> X => V:Val <_/k> <env_> X|->L <_/env> <store_> L|->V <_/store>


/*@ \subsection*{Variable/Array increment}

 This is tricky, because we want to allow all of {\tt ++x}, {\tt ++a[5]}
 Therefore, we need to extract the l-value of the expression to increment.
 To do that, we state that the expression to increment should be wrapped
 by the auxilliary ``l-value'' operation and then evaluated.
 The semantics of the auxilliary l-value operation is defined below.
 For now, all we need to know is that it takes an expression and evaluates
 to a location value, also introduced below with the auxilliary operations.
*/
  context ++([HOLE] => l-value([HOLE]))
  rule <k> ++loc(L) => I:Int +Int 1 <_/k>
       <store_> L |-> (I => I +Int 1) <_/store>

//@ \subsection*{Arithmetic operators}
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

/*@ \subsection*{Array lookup}

Untyped SIMPLE does not check array bounds
We prefer to use a helper computation item, lookup, to avoid locking the store */
  rule array(L,_)[N] => lookup(L +Int N) [structural]
  rule V[N1,N2,Vl] => V[N1][N2,Vl] [structural]
  syntax K ::= lookup Nat
  rule <k> lookup L => V <_/k> <store_> L |-> V <_/store>

//@ \subsection*{Size of an array}
  rule sizeOf(array(_,N)) => N

//@ \subsection*{Function call} The environment and the computation are pushed onto the stack
  rule <k> _`(_`)(function(L),Vl:List{Val}) ~> K => S ~> return(0); </k>
       <fstack> . => (Env,K) <_/fstack>
       <env> Env => GEnv[N..N+Nat|Xl| / getList{K}(Xl)] </env>
       <genv> GEnv:Map </genv>
       <store_> L |-> lambda(Xl,S) (. => N..N+Nat|Xl| |-> getList{K}(Vl)) <_/store>
       <nextLoc> N => N +Nat |Xl| </nextLoc>
  rule <k> return(V); ~> _ => V ~> K </k>
       <fstack> (Env,K) => . <_/fstack>
       <env> _ => Env </env>

//@ \subsection*{Read}
  rule <k> read() => I <_/k> <in> ListItem(I) => . <_/in>


------------------
//@ \section*{Statements}
------------------

//@ \subsection*{Empty blocks} One can make the rule below structural, if one doesn't want it to count as step
  rule {} => .

/*@ \subsection*{Nonempty Blocks} Make sure the environment is recovered after the block executes
 This rule can also be structural if one does not want entering a block to count as step */
  rule <k> {Ss:Stmts} => Ss~>env(Env) <_/k> <env> Env </env>

//@ \subsection*{Sequential composition}  Desugared into K's sequentialization.  Can also be structural
  rule S1:Stmt S2:Stmt => S1~>S2

/*@ \subsection*{Assignment}
 Like for increment, we first compute the l-value of the left-hand-side.
*/
  context ([HOLE] => l-value([HOLE]))=_
  rule <k> loc(L)=V => V <_/k> <store_> L|->(_=>V) <_/store>

/*@ \subsection*{l-value and loc}
 l-value(E) computes the l-value of E, where E can be an identifier X,
 or an array element A[I].

 l-value(E) evaluates to a location value of the form loc(L), where L is a natural number.
*/
  syntax Exp ::= l-value ( K )    --- for parsing reasons, we prefer to allow l-value to take a K
  syntax Val ::= loc ( Nat )
--- Local variable
  rule <k> l-value(X) => loc(L:Nat) <_/k> <env_> X|->L <_/env>
--- Array element: evaluate the array and its index; then the array lookup rule above applies.
  context l-value(_[_,`[HOLE`]:Exp,_])
  context l-value([HOLE][_])
--- Finally, return the address of the desired object member
  rule <k> l-value(lookup(L)) => loc(L) <_/k>


//@ \subsection*{Expression statements}  They are only used for their side effects, so their result is descarded
  rule V; => .

//@ \subsection*{Conditional}
  rule if  true then S else _ => S
  rule if false then _ else S => S

//@ \subsection*{While loop} Unrolled only at the top of the computation (to avoid non-termination)
  rule <k> while B:Exp do S  => if B then {S while B do S} else {} <_/k>

//@ \subsection*{Write}
  rule <k> write(I); => . <_/k> <out_> . => ListItem(I) </out>

//@ \subsection*{Exceptions}
  syntax ListItem ::= ( Id , Stmt , K , Map , List )
  syntax K ::= popx
  rule <k> (try S1 catch(X) S2 => S1 ~> popx) ~> K </k>
       <xstack> . => (X,S2,K,Env,FStack) <_/xstack>
       <env> Env </env>
       <fstack> FStack:List </fstack>
  rule <k> popx => . <_/k> <xstack> _:ListItem => . <_/xstack>
  rule <k> throw V; ~> _ => S2 ~> env(Env) ~> K </k>
       <xstack> (X,S2,K,Env,FStack) => . <_/xstack>
       <env> _ => Env[L/X] </env>
       <fstack> _ => FStack </fstack>
       <store_> . => L |-> V <_/store>
       <nextLoc> L => sNat L </nextLoc>

//@ \subsection*{Threads}
   rule <thread_> <k> spawn S => . <_/k> <env> Env </env> <_/thread>
        (. => <thread_> <k> S </k> <env> Env </env> <_/thread>)
   rule (<thread_> <k>.</k> <fstack>.</fstack> <holds> Holds:Map </holds> <_/thread> => .)
        <busy> Busy:Set => Busy -Set keys(Holds) </busy>
   rule <k>acquire V; => .<_/k> <holds_>. => V|->0<_/holds> <busy>Busy (.=>SetItem(V))</busy>
     if notBool(V in Busy)
   rule <k>acquire V; => .<_/k> <holds_>V|->(N => sNat N)<_/holds>
   rule <k>release V; => .<_/k> <holds_>V|->(sNat N => N)<_/holds>
   rule <k>release V; => .<_/k> <holds_>V|->0 => .<_/holds> <busy_>SetItem(V)=>.<_/busy>
   rule <k>rendezvous V; => .<_/k> <k>rendezvous V; => .<_/k>

----------------------------------------------
//@ \section*{Auxilliary declarations and operations}
----------------------------------------------

//@ \subsection*{Lists of values}
  syntax List{Val} ::= Val | List{Val} , List{Val} [ditto]
  syntax List{Exp} ::= List{Val}

//@ \subsection*{Length}
  syntax Nat ::= `| List{Id} `| [latex "\mid\!\!{#1}\!\mid"]
  macro |.List{Id}| = 0  
  macro |X,Xl| = sNat |Xl|

//@ \subsection*{Sequences of locations}
  syntax List{K} ::= Nat .. Nat
  rule N1:Nat..N1 => .List{K} [structural]
  rule N1..N2:Nat => N1,,sNat N1..N2 [structural]

//@ \subsection*{Environment recovery}
  syntax K ::= env ( Map )
  rule <k> env(Env) => . <_/k> <env> _ => Env </env> [structural]
  rule <k> V ~> (env(Env) => .) <_/k> <env> _ => Env </env> [structural]

//@ \subsection*{Pairing construct} Nedeed for stacking
  syntax ListItem ::=  ( Map , K )
endkm
