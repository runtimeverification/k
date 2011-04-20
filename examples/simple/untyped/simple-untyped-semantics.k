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
to define it. */

/*@ \subsubsection*{Values}
We here define the values of the language that the various fragments of
programs evaluate to.  First, integers and booleans are values.  As discussed,
arrays evaluate to special array reference values holding (1) a location from where
the array's elements are contiguously allocated in the store, and (2) the size
of the array.  Functions evaluate to function values as $\lambda$-abstractions
(we do not need to evaluate functions to closures because each function is executed
in the fixed global environment and function definitions cannot be nested). */

  syntax Val ::= Int | Bool
               | array ( Nat , Nat )
               | lambda ( List{Id} , Stmt ) [latex "\lambda{#1}\,.\,{#2}"]
  syntax Exp ::= Val

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
the top of the \textsf{k} cell). */

  syntax KResult ::= List{Val}

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

  configuration <T color="red">
                  <threads color="orange">
                    <thread multiplicity="*" color="yellow">
                      <k color="green"> K:K </k>
                      <control color="cyan">
                        <fstack color="blue"> .List </fstack>
                        <xstack color="purple"> .List </xstack>
                      </control>
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

/*@ \section*{Declarations and Initialization}
We start by defining the semantics of declarations (for variables, arrays and functions). */

/*@ \subsection*{Variable Declaration}
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

Note: The "trick" with using a \textsf{nextLoc} cell to generate fresh locations is
rather low level and hopefully temporary; we indend to soon allow instead a side-condition
of the form ``where $L$ fresh''. */

  context var X = [HOLE];
  rule <k> var X:Id = V; => . <_/k>
       <env> Env:Map => Env[L:Nat/X] </env>
       <store_> . => L|->V <_/store>
       <nextLoc> L => L +Nat 1 </nextLoc> 

/*@ \subsection*{Array Declaration}
SIMPLE allows multi-dimensional arrays.  For semantic simplicity, we desugar them all into
unidimensional arrays by code transformation.  This way, we will only need to give semantics
to unidimensional arrays.  The expressions given as array dimensions are first evaluated and
then the array is dynamically allocated the corresponding number of locations.  Thus, we can
dynamically allocate memory in SIMPLE by means of array declarations.  First, we need to
evaluate all the dimensions of the array: */

  context var X[_,`[HOLE`]:Exp,_];

/*@ The \K semantics of the uni-dimensional array declaration is somehow similar to the
above declaration of ordinary variables.  $N+1$ locations are allocated in the store
for an array of size $N$, the additional location (chosen to be the first one allocated)
holding the array reference value.  The array reference value \texttt{array(L,N)} states
that the array has size $N$ and its elements are located contiguously in the store starting
with location $L$.  Recall that $L..L'$ is the list of locations between $L$ and $L'$
and that $L..L'\mapsto V$ initializes each location in the list $L..L'$ to value $V$. */

  rule <k> var X[N:Nat]; => . <_/k>
       <env> Env => Env[L/X] </env>
       <store_> . => (L |-> array(L +Nat 1, N)) L +Nat 1 .. L +Nat 1 +Nat N |-> 0 <_/store>
       <nextLoc> L => L +Nat 1 +Nat N </nextLoc>

/*@ To desugar multi-dimensional arrays, we introduce two special unique variable
identifiers, \texttt{\$1} and \texttt{\$2}.  The first, \texttt{\$1},
is assigned the array reference value of the current array, so that we can redeclare
the array inside the loop body with fewer dimensions.  The second variable,
\texttt{\$2}, iterates through and initializes each element of the current dimension: */

  syntax Id ::= $1 | $2
  rule var X[N1,N2,Vl]; =>
       var X[N1];
       {
         var $1 = X;
         for $2 = 0 to _-_(N1,1) do   --- stupid parser
         {
           (var X[N2,Vl];)            --- stupid parser
           $1[$2] = X;
         }
       }  [structural]

/*@ Ideally, one would like to perform syntactic desugarings like above before we start
the actual semantics.  Unfortunately, that was not possible in this case because we
need to first evaluate the dimension expressions of the multi-dimensional array.
Indeed, the desugaring rule above does not work if the dimensions of the declared
array are arbitrary expressions, because they can have side effects
(e.g., \texttt{a[++x,++x]}) and those side effects would be propagated each time the
expression is evaluated in the desigaring code (note that both the loop condition and
the nested multi-dimensional declaration need to evaluate expressions given originally
array dimensions). */

/*@ \subsection*{Function declaration}
Functions are evaluated to $\lambda$-abstractions and stored like any other values
in the store.  A binding is added into the environment for the function name to the
location holding its body.  SIMPLE only allows function declarations at the top level
of the program, like $C$.  More precisely, the subsequent semantics of SIMPLE only works
well when one respects this requirement.  Indeed, the simplistic context-free parser
generated by the grammar above is more generous than we may want, in that it allows
function declarations anywhere any declaration is allowed, including inside arbitrary
blocks.  However, as the rule below shows, we are {\em not} storing the declaration
environment with the $\lambda$-abstraction value as closures do.  Instead, as seen
shortly, we switch to the global environment whenever functions are invoked, which
is consistent with our requirement that functions should only be declared at the top.
Thus, if one declares local functions, then one may see unexpected behaviors (e.g.,
when one shadows a global variable before declaring a local function).  The type
checker of SIMPLE, also defined in \K (see examples/simple/typed/static),
discards programs which do not respect this requirement. */

  rule <k> function F:Id(Xl:List{Id}) S:Stmt => . <_/k>
       <env> Env => Env[L/F] </env>
       <store_> . => L|->lambda(Xl,S) <_/store>
       <nextLoc> L => L +Nat 1 </nextLoc>

/*@ When we are done with the first pass (pre-processing), the computation cell
\textsf{k} contains only the token \texttt{execute} (see the module
SIMPLE-UNTYPED in file \texttt{simple-untyped.k}, which adds the token \texttt{extend}
at the end of the program) and the cell \textsf{genv} is empty.  In this case, we
have to call \texttt{main()} and to initialize the global environment by transfering the
contents of the local environment into it.  We prefer to do it this way, as oppossed to
processing all the top level declarations directly within the global environment, because
we want to avoid duplication of semantics: the syntax of the global declarations is
identical to that of their corresponding local declarations, so the semantics of the latter
suffices provided that we copy the local environment into the global one once we are done
with the pre-processing.  We want this separate pre-processing step precisely because we
want to create the global environment.  All (top-level) functions end up having their
names bound in the global environment and, as seen below, they are executed in that same
global environment; all these mean, in particular, that the functions ``see'' each other,
allowing for mutual recursion, etc. */

  syntax K ::= execute
  rule <k> execute => main(); </k> <env> Env </env> <genv> . => Env </genv>

/*@ \section*{Expressions}
We next define the \K semantics of all the expression constructs, in the order in which
their syntax was declared. */

/*@ \subsection*{Variable lookup}
When a variable $X$ is the first computational task (note the rupture of the \textsf{k} cell
to the right), and $X$ is bound to some location $L$ in the environment (note the rupture of
the \textsf{env} cell at both sides), and $L$ is mapped to some value $V$ in the store, then
rewrite $X$ by $V$: */

  rule <k> X => V:Val <_/k> <env_> X|->L <_/env> <store_> L|->V <_/store>

/*@ \subsection*{Variable/Array increment}
This is tricky, because we want to allow both {\tt ++x} and {\tt ++a[5]}.
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

/*@ \subsection*{Arithmetic operators}
There is nothing special about the following rules.  They rewrite the language constructs to their
library counterparts when their arguments become values of expected sorts: */

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
Untyped SIMPLE does not check array bounds (the dynamically typed version of it, in
examples/simple/typed/dynamic, does check for array out of bounds).  The first rule below
desugars multi-dimensional array access to uni-diminesional array access; recall that the
array access operation was declared strict, so all subexpressions involved are already
values at this stage.  The second rule rewrites the array access to a lookup operation
at a precise location; we prefer to do it this way to avoid locking the store.
Recall that ``--'' is an anonymous variable in \K matching any subterm (like in Prolog);
informally, ``there is something there but we don't care what''.
The semantics of the \texttt{lookup} operation is straighforward. */

  rule V[N1,N2,Vl] => V[N1][N2,Vl] [structural]
  rule array(L,_)[N] => lookup(L +Int N) [structural]
  syntax K ::= lookup ( Nat )
  rule <k> lookup(L) => V <_/k> <store_> L |-> V <_/store>

/*@ \subsection*{Size of an array}
The size of the array is stored in the array reference value, and the \texttt{sizeOf} construct
was declared strict, so: */

  rule sizeOf(array(_,N)) => N

/*@ \subsection*{Function call}
Function application was strict in both its arguments, so we can assume that both
the function and its arguments are evaluated to values (the former expected to be a
$\lambda$-abstraction).  The first rule below matches a well-formed function application
on top of the computation and performs the following steps atomically: it switches to the
function body followed by ``\texttt{return 0;}'' (a default return value for the case in
which the programmer forgot to return a value); it pushes the remaining computation and the
current environment onto the function stack (the remaining computation can thus also be
discarded from the computation cell, because an unavoidable subsequent \texttt{return}
statement will always recover it from the stack); it switches the current environment
(which is being pushed on the function stack) to the global environment, which is where
the free variables in the function body should be looked up; it binds the formal parameters
to fresh locations in the new environment, and stores the actual arguments to those locations
inthe store.  The second rule pops the computation and the environment from the stack when
a \texttt{return} statement is the next computational task, passing the returned value
to the poped computation (the popped computation was the context in which the returning
function was called). */

  syntax ListItem ::=  ( Map , K )
  rule <k> _`(_`)(lambda(Xl,S), Vl:List{Val}) ~> K => S ~> return(0); </k>
       <fstack> . => (Env,K) <_/fstack>
       <env> Env => GEnv[N..N+Nat|Xl| / getList{K}(Xl)] </env>
       <genv> GEnv:Map </genv>
       <store_> . => N..N+Nat|Xl| |-> getList{K}(Vl) <_/store>
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
endkm
