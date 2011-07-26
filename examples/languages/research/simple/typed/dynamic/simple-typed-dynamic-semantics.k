-------------------------------------
--- SIMPLE-TYPED-SEMANTICS module ---
-------------------------------------

module SIMPLE-TYPED-DYNAMIC-SEMANTICS
  imports SIMPLE-TYPED-DYNAMIC-DESUGARED-SYNTAX

/*@ Values that various fragments of programs evaluate to
*/

  syntax Val ::= Int | Bool  
               --- Array values are wrapped as specific reference values, where:
               --- 1st argument = the type of the array
               --- 2nd argument = the location of the first element in the array, and
               --- 3rd argument = the array size (array elements are contiguously allocated)
               | array ( Type , Nat , Nat ) 
               | lambda ( Type , List{Id} , Stmt ) 
                 [latex "\lambda{#2}.{#3}:{#1}"]

--- Values are expressions
  syntax Exp ::= Val 


-------------------------------------
--- Computations "swallow" syntax ---
-------------------------------------

  syntax KResult ::= List{Val}


---------------------
--- Configuration ---
---------------------

  configuration <T color="red">
                  <threads color="orange">
                    <thread multiplicity="*" color="yellow">
                      <k color="green"> K:K </k>
                      <control color="cyan">
                        <fstack color="blue"> .List </fstack>
                        <xstack color="purple"> .List </xstack>
                        <return color="LimeGreen"> none </return>    --- this cell holds the expecter return type
                      </control>
                      <env color="violet"> .Map </env>
                      <holds color="black"> .Map </holds>
                    </thread>
                  </threads>
                  <br/>
                  <genv color="pink"> .Map </genv>
                  <store color="white"> .Map </store>
                  <busy color="cyan">.Set</busy>
                  <in color="magenta"> .List </in>
                  <out color="brown"> .List </out>
                  <nextLoc color="gray"> 0 </nextLoc>
                </T>


---------------------------------------
--- Declarations and initialization ---
---------------------------------------

--- Variable declaration
  rule <k> var X:Id : Tp:Type ; => . ...</k>
       <env> Env:Map => Env[L:Nat/X] </env>
       <store>... . => L|->initVal(Tp) ...</store>     --- intialized with default value for its type
       <nextLoc> L => sNat(L) </nextLoc>

//@ \subsection{Array Declaration}
  rule <k> var X[N:Nat] : Tp[]; => . ...</k>
       <env> Env => Env[L/X] </env>
       <store>... . => L |-> array(Tp[], sNat L, N) ...</store>
       <nextLoc> L => sNat L +Nat N </nextLoc>

  context var X[_,[#]:Exp,_] : Tp[];


  syntax Id ::= $1 | $2
  rule var X[N1,N2,Vl] : Tp[] ; =>
       var X[N1] : Tp[] ;
       {
         var $1 : Tp[] = X;
         for $2 = 0 to _-_(N1,1) do   --- stupid parser
         {
           (var X[N2,Vl] : Tp ;)            --- stupid parser
           $1[$2] = X;
         }
       }  [structural]




//@\subsection{Function declaration}
  rule <k> function F:Id(XTl:List{IdType}) : Tp S:Stmt => . ...</k>
       <env> Env => Env[L/F] </env>
       <store>... . => L|->lambda(typeList(XTl)->Tp,idList(XTl),S) ...</store>
       <nextLoc> L => L +Nat 1 </nextLoc>

--- When we are done with the first pass (preprocessing), i.e., the computation
--- and genv are empty, call main() and initialize the global environment
  syntax K ::= execute
  rule <k> execute => main(); </k> <env> Env </env> <genv> . => Env </genv>


//@\section{Expressions}

//@\subsection{Variable lookup}
  rule <k> X => V:Val ...</k> <env>... X|->L ...</env> <store>... L|->V ...</store>

//@\subsection{Variable/Array increment}

  context '++_([#]:K => l-value([#]))

  rule <k> '++_(loc(L)) => I:Int +Int 1 ...</k>
       <store>... L |-> (I => I +Int 1) ...</store>

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

/*@ \subsection{Array lookup}
  Note that we check the array bounds now
  We prefer to use a helper computation item, lookup, to avoid locking the store
*/
  rule V[N1,N2,Vl] => V[N1][N2,Vl] [structural]
  rule <k> array(_,L,M:Nat)[N] => lookup(L +Int N) ...</k> if N >=Nat 0 andBool N <=Nat M [structural]
  syntax K ::= lookup ( Nat )
  rule <k> lookup(L) => V ...</k> <store>... L |-> V ...</store>

//@\subsection{Size of array}
  rule sizeOf(array(_,_,N)) => N

/*\subsection{Function call}
 The environment, the computation and current return type are pushed onto the stack
*/

  syntax ListItem ::=  ( Map , K , Bag )


  rule <k> _`(_`)(lambda(Tpl:List{Type}->Tp,Xl:List{Id},S),Vl:List{Val}) ~> K => S ~> return(initVal(Tp)); </k>
       <control>
         <fstack> . => (Env,K,<return> Tp' </return> C) ...</fstack>
         <return> Tp':Type => Tp </return>
         C:Bag
       </control>
       <env> Env => GEnv[N..N+Nat|Xl| / getList{K}(Xl)] </env>
       <genv> GEnv:Map </genv>
       <store>... (. => N..N+Nat|Xl| |-> getList{K}(Vl)) ...</store>
       <nextLoc> N => N +Nat |Xl| </nextLoc>
    if typeOf(Vl) ==Bool Tpl

--- Function return.  We define it here because it is related to the above
  rule <k> return(V); ~> _ => V ~> K </k>
       <control> 
         <fstack> (Env,K,C) => . ...</fstack>
         (<return> Tp </return> _ => C)
       </control>
       <env> _ => Env </env>
    if typeOf(V) ==Bool Tp

//@\subsection{Read}
  rule <k> read() => I ...</k> <in> ListItem(I) => . ...</in>

//@\subsection{Assignment}

  context ([#]:Exp => l-value([#]:Exp)) = _

  rule <k> loc(L)=V1 => V1 ...</k> <store>... L|->(V2=>V1) ...</store>
    if typeOf(V1) ==Bool typeOf(V2) 


//@\section{Statements}

/*@\subsection{Empty blocks}
 One can make the rule below structural, if one doesn't want it to count as step
*/
  rule {} => .

/*@\subsection{Nonempty Blocks}
 Make sure the environment is recovered after the block executes
 This rule can also be structural if one does not want entering a block to count as step
*/
  rule <k> {Ss:Stmts} => Ss~>env(Env) ...</k> <env> Env </env>


//@ Environment recovery:
  syntax K ::= env ( Map )
  rule <k> env(Env) => . ...</k> <env> _ => Env </env> [structural]

  rule (env(_) => .) ~> env(_) [structural]

/*@\subsection{Sequential composition}
  Desugared into K's sequentialization.  Can also be structural
*/
  rule S1:Stmt S2:Stmt => S1~>S2

/*@\subsection{Expression statements}
  They are only used for their side effects, so their result is descarded
*/
  rule V; => .

//@\subsection{Conditional}
  rule if true  then S else _ => S
  rule if false then _ else S => S

/*@\subsection{While loop}
Semantics by unrolling the loop at the top of the computation (to avoid non-termination).
*/
  rule <k> while B:Exp do S  => if B then {S while B do S} else {} ...</k>

//@\subsection{Write}
  rule <k> write(I); => . ...</k> <out>... . => ListItem(I) </out>

//@ \subsection{Exceptions}


  syntax ListItem ::= ( IdType , Stmt , K , Map , Bag )
  syntax K ::= popx
  rule <k> (try S1 catch(XT) S2 => S1 ~> popx) ~> K </k>
       <control> <xstack> . => (XT,S2,K,Env,C) ...</xstack> C:Bag </control>
       <env> Env </env>
  rule <k> popx => . ...</k> <xstack> _:ListItem => . ...</xstack>
  rule <k> throw V; ~> _ => {var XT=V; S2} ~> K </k>
       <control> <xstack> (XT:IdType,S2,K,Env,C) => . ...</xstack> (_ => C) </control>
       <env> _ => Env </env>

//@ \subsection{Threads}

//@ \subsubsection{Thread creation}

   rule <thread>... <k> spawn S => . ...</k> <env> Env </env> ...</thread>
        (. => <thread>... <k> S </k> <env> Env </env> ...</thread>)

//@ \subsubsection{Thread termination}

   rule (<thread>... <k>.</k> <holds> H:Map </holds> ...</thread> => .)
        <busy> Busy:Set => Busy -Set keys(H) </busy>

//@ \subsubsection{Acquire lock}

   rule <k> acquire V; => . ...</k> <holds>... . => V|->0 ...</holds>
        <busy> Busy (. => SetItem(V)) </busy>
     if notBool(V in Busy) [tags nondet]
   rule <k> acquire V; => . ...</k> <holds>... V|->(N => N +Nat 1) ...</holds>

//@ \subsubsection{Release lock}

   rule <k> release V; => . ...</k> <holds>... V|->(N => _-Int_(N,1)) ...</holds>
     if N >Nat 0
   --- used prefix notation for -Int because of parsing problems
   rule <k> release V; => . ...</k> <holds>... V|->0 => . ...</holds>
        <busy>... SetItem(V)=>. ...</busy>

//@ \subsubsection{Rendezvous synchronization}

   rule <k> rendezvous V; => . ...</k> <k> rendezvous V; => . ...</k> [tags nondet]

//@\section{Auxilliary declarations and operations}

//@\subsection{Initial value for each type}
  syntax Val ::= none | initVal ( Type )
/*
  macro initVal(int) = 0
  macro initVal(bool) = false
  macro initVal(void) = none
  macro initVal(Tp[]) = array(Tp[],0,0)
  macro initVal(Tpl->Tp) = lambda(Tpl->Tp,.List{Bottom},{})
*/

//@\subsection{Type of each value and of list of values}
  syntax List{Type} ::= typeOf ( List{Val} )  
  macro typeOf(initVal(Tp)) = Tp 
  macro typeOf(I) = int
  macro typeOf(T) = bool
  macro typeOf(none) = void
  macro typeOf(lambda(Tp, _, _)) = Tp
  macro typeOf(array(Tp,_,_)) = Tp
  macro typeOf(V1,V2,Vl) = _`,_(typeOf(V1),typeOf(V2,Vl))
  macro typeOf(.List{Bottom}) = .List{Bottom}

//@ \subsection{l-value and loc}

--- For parsing reasons, we prefer to allow l-value to take a K
  syntax Exp ::= l-value ( K )
  syntax Val ::= loc ( Nat )
--- Local variable
  rule <k> l-value(X) => loc(L:Nat) ...</k> <env>... X|->L ...</env>
--- Array element: evaluate the array and its index;
--- then the array lookup rule above applies.
  context l-value(_[_,[#]:Exp,_])
  context l-value([#][_])
--- Finally, return the address of the desired object member
  rule <k> l-value(lookup(L)) => loc(L) ...</k>

//@\subsection{Length}
  syntax Nat ::= `| List{Id} `| [latex "\mid\!\!{#1}\!\mid"]
  macro |.List{Bottom}| = 0  
  macro |X,Xl| = sNat |Xl|

//@\subsection{Sequences of locations}
  syntax List{K} ::= Nat .. Nat
  rule N1:Nat..N1 => .List{K} [structural]
  rule N1..N2:Nat => N1,,sNat N1..N2 [structural]


//@\subsection{Lists of values}
  syntax List{Val} ::= Val | List{Bottom} | List{Val} , List{Val} [ditto]
  syntax List{Exp} ::= List{Val}

/*@\subsection{List extractors}
Extracting lists of corresponding untyped names and of types from a list of typed names
*/
  syntax List{Id} ::= idList ( List{IdType} )
  macro idList(.List{Bottom}) = .List{Bottom}
  macro idList(X : Tp, XTl) = _`,_(X, idList(XTl))

  syntax List{Type} ::= typeList ( List{IdType} )
  macro typeList(.List{Bottom}) = .List{Bottom}
  macro typeList(X : Tp, XTl) = _`,_(Tp, typeList(XTl))
end module
