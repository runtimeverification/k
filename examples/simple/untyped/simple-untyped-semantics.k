---------------------------------------
--- SIMPLE-UNTYPED-SEMANTICS module ---
---------------------------------------

kmod SIMPLE-UNTYPED-SEMANTICS is including SIMPLE-UNTYPED-DESUGARED-SYNTAX + K

/*@ \section*{Basic Semantic Infrastructure}
Before one starts adding semantic rules to a \K definition, one needs to
define the basic semantic infrastructure consisting of definitions for {\em values},
{\em computations} and the {\em configuration}.  The values are needed to know when to
stop applying the heating rules corresponding to strictness or context declarations;
unfortunately, values cannot be detected automatically, so one cannot avoid this step.
The computation structures, or simply computations, are needed to properly include the
language syntax under the K sort, as the \K semantics operates only on terms of sort $K$;
fortunately, this can be done mostly automatically, except for the special result
computations.  Finally, the configuration serves as a backbone for the process of
configuration abstraction which allows users to only mention the relevant cells in each
semantic rule, the rest of the configuration context being infered automatically; the
configuration could arguably be automatically infered from the rules, but it turned out
that it is very useful for language designers/semanticists to actually think of and
design their configuration explicitly, so the current implementation of \K requires one
to define it.
*/

-------------------------------------------------------------
/*@ \subsubsection*{Values}
We here define the values of the language that the various fragments of
programs evaluate to.
First, integers and booleans are values.  As discussed, arrays evaluate
to special array reference values holding (1) a location from where the
array's elements are contiguously allocated in the store, and (2) the size
of the array.  Similarly, functions evaluate to function reference values
telling where the actual function body is stored (we do not need to evaluate
functions to closures because each function is executed in the fixed global
environment (function definitions cannot be nested).  We also need to
define a value construct for the function body, namely a
{\em $\lambda$-abstraction}.  Working with array and function references
makes the language more efficient, because reference values are small. */
-------------------------------------------------------------

  syntax Val ::= Int | Bool
               | array ( Nat , Nat )
               | function( Nat )
               | lambda ( List{Id} , Stmt ) [latex "\lambda{#1}\,.\,{#2}"]

--- the values are expressions
  syntax Exp ::= Val


-------------------------------------
/*@ \subsubsection*{Computations}
Recall that in \K, the {\em computational structures} or simply {\em computations}
``swallow'' the entire language syntax.  Thus, every fragment of program is a
particular computation, that is, a term of sort $K$.  Also, recall that computations
have quite a simple syntax: abstract syntax trees (where the original language constructs
become AST node labels, i.e., constants of sort $\KLabel$) extended with the special
{\em task sequentialization} construct $K ::= K \kra K$.  In addition to the sorts
$K$ and $\KLabel$, \K also has one more important sort related to computations, namely
$\KResult$.  Distinguishing terms of sort $\KResult$ is not necessary in theory, but it
is crucial in \K tools, because they interpret such terms as irreducible and thus know
when to stop the heating process associated to the strictness attributes.
Below we state that all lists of values are terms of sort $\KResult$.  We use lists of
values instead of values because, as discussed above, we want lists of expressions
to evaluate to lists of values whenever scheduled for evaluation (by placing them on
the top of the \textsf{k} cell).
*/
-------------------------------------
  syntax KResult ::= List{Val}


---------------------
/*@ \subsection*{Configuration}
The \K configuration of SIMPLE consists of a top level cell, \textsf{T},
holding a \textsf{threads} cell, a global environment map cell \textsf{genv}
mapping the global variables and function names to their locations, a shared
store map cell \textsf{store} mapping each location to some value, a set cell
\textsf{busy} holding the locks which have been acquired but not yet released
by threads, \textsf{input} and \textsf{output} list cells, and a
\textsf{nextLoc} cell holding a natural number indicating the next available
location (one can think of locations as symbolic entities; e.g., location 17
means the 17'th allocated location, which in implementations of the language
may be different from memory cell 17 or may even be the same memory cell that
was previously allocated and then freed).  The \textsf{threads} cell contains
one \textsf{thread} cell for each existing thread in the program.  Note that
the thread cell has multiplicity ``*'', which means that at any given moment
there could be zero, one or more \textsf{thread} cells.  Each \textsf{thread}
cell contains a computation cell \textsf{k}, a function stack \textsf{fstack}
which is a list, an exception stack \textsf{xstack} which is also a list, a
local environment map cell \textsf{env} mapping the thread local variables to 
locations in the store, and finally a \textsf{holds} map cell indicating
what locks have been acquired by the thread and not released so far and how
many times (SIMPLE's locks are re-entrant).  Note that all cells except for
\textsf{k} are also initialized, in that they contain a ground term of their
corresponding sort.  The \textsf{k} cell needs not be initialized at this level,
because it will be initialized with the program to evaluate later. */
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
/*@ \section*{Declarations and Initialization}
We start by defining the semantics of declarations (for variables, arrays and functions).
The trickiest of the rules below is the one for desugaring multi-dimensional arrays into
uni-dimensional arrays.
*/
---------------------------------------

/*@ \subsection*{Variable declaration}
The SIMPLE syntax was desugared above so that each variable is declared alone and is also
initialized.  The context declaration below says that the expression used for the initilization
of the variable should be first evaluated (that expression can be any arithmetic expression,
including array lookups, function calls, etc.).  The semantic rule below matches resulting
variable declarations of the form ``$\texttt{var}\,X\,\texttt{=}\,V\texttt{;}$'' (with $V$ a
value) on top of the \textsf{k} cell (indeed, note that the \textsf{k} cell is complete,
or round, to the left, and is torn, or ruptured, to the right), allocates a fresh location
$L$ in the store to hold the value $V$ (indeed, the unit ``$\kdot$'', or nothing, is matched
anywhere in the map---note the tears at both sides---and replaced with the mapping
$L\mapsto V$), and binds $X$ to $L$ in the local environment shadowing previous declarations
of $X$, if any.  It is this possible shadowing of $X$ which dissallows us to use a similar
technique for updating the environment as for updating the store, as we know that $L$ is not
already bound in the store when we add $L \mapsto V$.  We prefer the approach used for updating
the store whenever possible, because it offers more true concurrency than the latter; indeed,
according to the concurrent semantics of $K$, the store is not frozen while $L\mapsto V$ is
added to it, while the environment is frozen during the update operation $\textit{Env}[L/X]$.
The variable declaration command is also removed from the top of the computation cell
and the fresh location counter is incremented.  All the above happen in one step, with the rule
below.  Note also how configuration abstraction allows us to only mention the needed cells;
indeed, as the configuration above states, the \textsf{k} and \textsf{env} cells are actually
located within a \textsf{thread} cell within the \textsf{threads} cell, but one needs not mention
these: the configuration context of the rule is automatically transformed to match the declared
configuration structure.
*/
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
