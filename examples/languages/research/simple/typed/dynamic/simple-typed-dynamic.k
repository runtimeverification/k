module SIMPLE-TYPED-DYNAMIC-SYNTAX

/*@ \section{Syntax}
The syntax of typed SIMPLE extends that of untyped SIMPLE with support
for declaring types to variables and functions.  The syntax below is identical
to that of the static semantics of typed SIMPLE.  However, the \K
strictness attributes are like those of the untyped SIMPLE, to capture
the desired evaluation strategies of the various language constructs .  */

  syntax #Id ::= "main"

//@ \subsection{Types}

  syntax Type ::= "int"
                | "bool"
                | "string"
                | "void"
                | "array" "of" Type [:prec(1):]
                | "function" "from" Types "to" Type
                    [:prec(1) latex "{#1}\rightarrow{#2}":]
  syntax Types ::= List{Type,","}

//@ \subsection{Declarations}

  syntax Decl ::= "var" Exps ";"
                | "function" #Id "(" Exps ")" ":" Type Stmt

//@ \subsection{Expressions}

  syntax Exp ::= #Int | #Bool | #String | #Id
               | "++" Exp              [:prec 0:]
               | Exp "+" Exp           [:strict prec(33) gather(E e):]
               | Exp "-" Exp           [:strict prec(33) gather(E e):]
               | Exp "*" Exp           [:strict prec(31) gather(E e):]
               | Exp "/" Exp           [:strict prec(31) gather(E e):]
               | Exp "%" Exp           [:strict prec(31) gather(E e):]
               | "-" Exp               [:strict:]
               | Exp "<" Exp           [:strict prec(37):]
               | Exp "<=" Exp          [:strict prec(37):]
               | Exp ">" Exp           [:strict prec(37):]
               | Exp ">=" Exp          [:strict prec(37):]
               | Exp "==" Exp          [:strict prec(37):]
               | Exp "!=" Exp          [:strict prec(37):]
               | Exp "and" Exp         [:strict prec(55) gather(E e):]
               | Exp "or" Exp          [:strict prec(59) gather(E e):]
               | "not" Exp             [:strict prec(53):]
               | Exp "[" Exps "]"      [:strict prec(1):]
               | "sizeOf" "(" Exp ")"  [:strict:]
               | Exp "(" Exps ")"      [:strict prec(2):]
               | "read" "(" ")"
               | Exp "=" Exp           [:strict(2) prec(40) gather (e E):]

               | Exp ":" Type          [:prec(10):]
                                       // allowed only for declarations
  syntax Exps ::= List{Exp,","}

//@ \subsection{Statements}

  syntax Stmt ::= "{" "}"
                | "{" Stmts "}"
                | Exp ";"                               [:strict prec(45):]
                | "if" Exp "then" Stmt "else" Stmt      [:strict(1) prec(90):]
                | "if" Exp "then" Stmt                  [:prec(89):]
                | "while" Exp "do" Stmt                 [:prec(90):]
                | "for" #Id "=" Exp "to" Exp "do" Stmt  [:prec(90):]
                | "return" Exp ";"                      [:strict:]
                | "return" ";"
                | "print" "(" Exps ")" ";"              [:strict:]
                | "try" Stmt "catch" "(" #Id ")" Stmt   [:prec(90):]
                | "throw" Exp ";"                       [:strict:]
                | "spawn" Stmt                          [:prec(90):]
                | "acquire" Exp ";"                     [:strict:]
                | "release" Exp ";"                     [:strict:]
                | "rendezvous" Exp ";"                  [:strict:]

  syntax Stmts ::= Decl | Stmt
                 | Stmts Stmts                         [:prec(100) gather(e E):]

//@ We use the same desugaring macros like in typed SIMPLE

  macro if E:Exp then S:Stmt = if E then S else {}
  macro (for X = E1 to E2 do S) = {var X:int=E1; while X <= E2 do {S X=X+1;}}
  macro var E1:Exp, E2:Exp, Es:Exps; = var E1; var E2, Es;
  macro var X:#Id : T:Type = E; = var X : T; X = E;
end module


module SIMPLE-TYPED-DYNAMIC
  imports SIMPLE-TYPED-DYNAMIC-SYNTAX

//@ \section{Values and results}

  syntax Val ::= #Int | #Bool | #String
               | "array" "(" Type "," #Nat "," #Nat ")"
               | "lambda" "(" Exps "," Stmt "," Type ")"
  syntax Exp ::= Val
  syntax KResult ::= Val

//@ \section{Configuration}

  configuration <T color="red">
                  <threads color="orange">
                    <thread multiplicity="*" color="yellow">
                      <k color="green"> ($PGM:K ~> execute) </k>
                      <control color="cyan">
                        <fstack color="blue"> .List </fstack>
                        <xstack color="purple"> .List </xstack>
                        <return color="LimeGreen"> none </return>
                          // holds return type
                       </control>
                      <env color="violet"> .Map </env>
                      <holds color="black"> .Map </holds>
                    </thread>
                  </threads>
                  <br/>
                  <genv color="pink"> .Map </genv>
                  <store color="white"> .Map </store>
                  <busy color="cyan">.Set</busy>
                  <in color="magenta" stream="stdin"> .List </in>
                  <out color="brown" stream="stdout"> .List </out>
                  <nextLoc color="gray"> 0 </nextLoc>
                </T>


//@ \section{Declarations and Initializations}

//@ The ``undefined'' construct is now parameterized by the type.

  syntax K ::= "undefined" "(" Type ")" [:latex("\bot_{#1}"):]

  rule <k> var X:#Id : T:Type; => . ...</k>
       <env> Env:Map => Env[L:#Nat/X] </env>
       <store>... . => L |-> undefined(T) ...</store>
       <nextLoc> L => L +Nat 1 </nextLoc>

/*@ Block if the type of an array declaration is not
of the form \texttt{array of $T$}. */

  rule <k> var X[N:#Nat] : array of T; => . ...</k> 
       <env> Env => Env[L/X] </env>
       <store>... . => L |-> array(T, L +Nat 1, N)
                       L +Nat 1 .. L +Nat N |-> undefined(T) ...</store>
       <nextLoc> L => L +Nat 1 +Nat N </nextLoc>

  context var X[[HOLE]];

//@ Make sure all declared variables have the right types.

  syntax #Id ::= "$1" | "$2"
  rule var X[N1,N2,Vl] : array of array of T; =>
       var X[N1] : array of array of T;
       {
         var $1 : array of array of T = X;
         for $2 = 0 to _-_(N1,1) do       // stupid parser
         {
           (var X[N2,Vl] : array of T;)   // stupid parser
           $1[$2] = X;
         }
       }  [:structural:]

/*@ Store all function parameters, as well as the return type, as part
of the lambda abstraction.  In the spirit of dynamic typing, we will
make sure that parameters are well typed when the function is invoked. */

  rule <k> function F:#Id(XTs:Exps) : T S:Stmt => . ...</k>
       <env> Env => Env[L/F] </env>
       <store>... . => L |-> lambda(XTs,S,T) ...</store>
       <nextLoc> L => L +Nat 1 </nextLoc>

//@ When done with the first pass, call \texttt{main()}.

  syntax K ::= "execute"
  rule <k> execute => main(); </k> <env> Env </env> <genv> . => Env </genv>


//@ \section{Expressions}

  rule <k> X => V:Val ...</k> <env>...X|->L...</env>
       <store>...L|->V...</store> [:transition:]

  context ++([HOLE] => l-value([HOLE]))

  rule <k> ++loc(L) => I:#Int +Int 1 ...</k>
       <store>... L |-> (I => I +Int 1) ...</store> [:transition:]

  rule I1:#Int + I2:#Int => I1 +Int I2
  rule Str1:#String + Str2:#String => Str1 +String Str2
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
  rule B1:#Bool and B2:#Bool => B1 andBool B2
  rule B1 or B2 => B1 orBool B2
  rule not(B:#Bool) => notBool(B)

//@ Check array bounds, as part of the dynamic typing policy.

  rule V[N1,N2,Vl] => V[N1][N2,Vl] [:structural:]
  rule array(_,L,M:#Nat)[N] => lookup(L +Int N)
    if N >=Nat 0 andBool N <Nat M   [:structural:]
  rule sizeOf(array(_,_,N)) => N

//@ Define function call and return together, to see their relationship.

  syntax Vals ::= List{Val,","}
  syntax ListItem ::=  "(" Map "," K "," Bag ")"
  rule <k> _`(_`)(lambda(XTs,S,T),Vs) ~> K => bindto(XTs,Vs) ~> S ~> return; </k>
       <control>
         <fstack> . => (Env, K, <return> T' </return> C) ...</fstack>
         <return> T':Type => T </return>
         C:Bag
       </control>
       <env> Env => GEnv </env>
       <genv> GEnv:Map </genv>

  rule <k> return V; ~> _ => V ~> K </k>
       <control>
         <fstack> (Env,K,C) => . ...</fstack>
         (<return> T </return> _ => C)
       </control>
       <env> _ => Env </env>
    if typeOf(V) ==Bool Tp

  syntax Val ::= "nothing"
  rule return; => return nothing;   [: structural :]

//@ \section{Statements}

  rule {} => . [:structural:]
  rule <k> {Ss:Stmts} => Ss~>env(Env) ...</k> <env> Env </env> [:structural:]
  rule S1:Stmt S2:Stmt => S1 ~> S2
  rule V; => .
  rule if  true then S else _ => S
  rule if false then _ else S => S
  rule <k> while E:Exp do S
    => if E then {S while E do S} else {} ...</k> [:structural:]
// decide if we want to only print integers and strings
  rule <k> print(V,Vl=>Vl);...</k> <out>... .=>ListItem(V)</out> [:transition:]
  rule print(); => . [:structural:]

  syntax ListItem ::= "(" #Id "," Stmt "," K "," Map "," Bag ")"
  syntax K ::= "popx"
  rule <k> (try S1 catch(X : T) S2 => S1 ~> popx) ~> K </k>
       <control> <xstack> . => (X : T,S2,K,Env,C) ...</xstack> C:Bag </control>
       <env> Env </env>
  rule <k> popx => . ...</k> <xstack> _:ListItem => . ...</xstack>
  rule <k> throw V; ~> _ => {var X : T = V; S2} ~> K </k>
       <control> <xstack> (X : T,S2,K,Env,C) => . ...</xstack> (_ => C) </control>
       <env> _ => Env </env>

   rule <thread>... <k> spawn S => . ...</k> <env> Env </env> ...</thread>
        (. => <thread>... <k> S </k> <env> Env </env> ...</thread>)
   rule (<thread>... <k>.K</k> <holds> H:Map </holds> ...</thread> => .)
        <busy> Busy:Set => Busy -Set keys(H) </busy>
   rule <k> acquire V; => . ...</k> <holds>... . => V|->0 ...</holds>
        <busy> Busy (. => SetItem(V)) </busy>
     if notBool(V in Busy)   [:transition:]
   rule <k> acquire V; => . ...</k> <holds>... V|->(N => N +Nat 1) ...</holds>
   rule <k> release V; => . ...</k> <holds>... V|->(N => _-Int_(N,1)) ...</holds>
     if N >Nat 0
   // used prefix notation for -Int because of parsing problems
   rule <k> release V; => . ...</k> <holds>... V|->0 => . ...</holds>
        <busy>... SetItem(V)=>. ...</busy>
   rule <k> rendezvous V; => . ...</k> <k> rendezvous V; => . ...</k> [:transition:]

//@ \subsection{Auxiliary operations}

// For parsing reasons, we prefer to allow l-value to take a K
  syntax Exp ::= "l-value" "(" K ")"
  syntax Val ::= "loc" "(" #Nat ")"
// Local variable
  rule <k> l-value(X) => loc(L:#Nat) ...</k> <env>... X|->L ...</env>
// Array element: evaluate the array and its index;
// then the array lookup rule above applies.
  context l-value(_[[HOLE]])
  context l-value([HOLE][_])
// Finally, return the address of the desired object member
  rule <k> l-value(lookup(L)) => loc(L) ...</k>

  syntax K ::= "lookup" "(" #Nat ")"
  rule <k> lookup(L) => V ...</k> <store>... L |-> V ...</store> [:transition:]

//@ \texttt{bindto} also checks the well-formedness of the function parameters

  syntax K ::= "bindto" "(" Exps "," Vals ")"
  rule <k> bindto((X : T, XTs:Exps => XTs),(V,Vs:Vals => Vs)) ...</k>
       <env> Env => Env[L/X] </env>
       <store>... . => L |-> V ...</store>
       <nextLoc> L => L +Nat 1 </nextLoc>
    if typeOf(V) ==Bool T
  rule <k> bindto(.Exps,.Vals) => . ...</k>

  rule <k> read() => I ...</k> <in> ListItem(I) => . ...</in> [:transition:]

  context ([HOLE] => l-value([HOLE])) = _
  rule <k> loc(L)=V => V ...</k> <store>... L |-> (K => V) ...</store>
    if typeOf(V) ==Bool typeOf(K:K)   [:transition:]

  syntax K ::= "env" "(" Map ")"
  rule <k> env(Env) => . ...</k> <env> _ => Env </env> [:structural:]
  rule (env(_) => .) ~> env(_) [:structural:]




//@ \subsection{Sequences of locations}

  syntax List{K} ::= #Nat ".." #Nat
  rule N1:#Nat..N2:#Nat => .List{K}              if N1  >Nat N2 [:structural:]
  rule N1:#Nat..N2:#Nat => N1 ,, (N1 +Nat 1)..N2 if N1 <=Nat N2 [:structural:]


end module
