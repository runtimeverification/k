module SIMPLE-TYPED-DYNAMIC-SYNTAX

/*@ \section{Syntax}
The syntax of typed SIMPLE extends that of untyped SIMPLE with support
for declaring types to variables and functions.  The syntax below is identical
to that of the static semantics of typed SIMPLE.  However, the \K
strictness attributes are like those of the untyped SIMPLE, to capture
the desired evaluation strategies of the various language constructs .  */

//@ \subsection{Types}

  syntax Type ::= "int"
                | "bool"
                | "string"
                | "void"
                | "arrayOf" Type
                    [latex("{#1}\texttt{\char91\char93}")]
                | "function" "from" Types "to" Type
                    [latex("({#1}\ \texttt{->}\ {#2})")]

  syntax Types ::= List{Type,","}  [strict]

//@ \subsection{Declarations}

  syntax Decl ::= "var" Exps ";"
                | "function" Id "(" Exps ")" ":" Type Stmt

//@ \subsection{Expressions}


  syntax Exp ::= Int | Bool | String | Id
               | "(" Exp ")"            [bracket]
               | "++" Exp     
               > Exp "[" Exps "]"       [strict]
               > Exp "(" Exps ")"       [strict]
               | "-" Exp                [strict]
               | "sizeOf" "(" Exp ")"   [strict]
               | "read" "(" ")"    
               > left:
                 Exp "*" Exp             [strict, left]
               | Exp "/" Exp             [strict, left]
               | Exp "%" Exp             [strict, left]
               > left:
                 Exp "+" Exp             [strict, left]
               | Exp "-" Exp             [strict, left]
               > non-assoc:
                 Exp "<" Exp             [strict, non-assoc]
               | Exp "<=" Exp            [strict, non-assoc]
               | Exp ">" Exp             [strict, non-assoc]
               | Exp ">=" Exp            [strict, non-assoc]
               | Exp "==" Exp            [strict, non-assoc]
               | Exp "!=" Exp            [strict, non-assoc]
               > "not" Exp               [strict]
               > left:
                 Exp "and" Exp           [strict, left]
               | Exp "or" Exp            [strict, left]
               > Exp "=" Exp             [strict(2), right]
               | Exp ":" Type           // allowed only for declarations
//               | Exp "of" Type           // allowed only for declarations

  syntax Exps ::= List{Exp,","}

//@ \subsection{Statements}

  syntax Stmt ::= "{" "}"
                | "{" Stmts "}"
                | Exp ";"                               [strict]
                | "if" Exp "then" Stmt "else" Stmt      [avoid, strict(1)]
                | "if" Exp "then" Stmt  
                | "while" Exp "do" Stmt
                | "for" Id "=" Exp "to" Exp "do" Stmt
                | "return" Exp ";"                      [strict]
                | "return" ";"
                | "print" "(" Exps ")" ";"              [strict]
                | "try" Stmt "catch" "(" Id ")" Stmt 
                | "throw" Exp ";"                       [strict]
                | "spawn" Stmt 
                | "acquire" Exp ";"                     [strict]
                | "release" Exp ";"                     [strict]
                | "rendezvous" Exp ";"                  [strict]

  syntax Stmts ::= Decl | Stmt
                 | Stmts Stmts                      [right]


//@ We use the same desugaring macros like in typed SIMPLE

  rule if E:Exp then S:Stmt => if E then S else {}
  rule (for X:Id = E1:Exp to E2:Exp do S:Stmt)
        =>
       {var X : int = E1; while X <= E2 do {S X = (X + 1);}}
  rule var E1:Exp, E2:Exp, Es:Exps; => var E1; var E2, Es;
  rule var (X:Id : T:Type) = E:Exp;
       =>
       var X : T; X = E;
endmodule


module SIMPLE-TYPED-DYNAMIC
  imports SIMPLE-TYPED-DYNAMIC-SYNTAX

//@ \section{Semantics}

/*@ \subsection{Values and results}
These are similar to those of untyped SIMPLE, except that the array
references and the function abstrations now also hold their types.
These types are needed in order to easily compute the type of any
value inthe language (see the auxiliary \texttt{typeOf} operation at
the end of this module).  Note that our more-generous-than-needed
syntax here allows function abstractions to take a list of expressions
as parameters; in fact, the semantics will be given in a way that
those expressions can only be typed identifiers.  Recall that the
purpose of syntax in a \K definition is not to parse programs in order
to reject those not satisfying the expected syntactic/typing
conventions (this is what a static semantics does---see the statically
typed SIMPLE), but only to parse programs ``enough'' to give them
semantics.  In other words, the \K syntax is the ``syntax of the
semantics''.  */

  syntax Val ::= Int | Bool | String
               | "arrayRef" "(" Type "," Int "," Int ")"
               | "lambda" "(" Exps "," Stmt "," Type ")"
                     [latex("(\lambda{#1}\,.\,{#2}):{#3}")]
  syntax Vals ::= List{Val,","}
  syntax Exp ::= Val
  syntax KResult ::= Val

/*@ \subsection{Configuration}
The configuration is almost identical to that of untyped SIMPLE,
except for a \textsf{return} cell inside the \textsf{control} cell.
This \textsf{return} cell will hold, like in the static semantics of
typed SIMPLE, the expected type of the value returned by the function
being executed.  The contents of this cell will be set whenever a
function is invoked and will be checked whenever the evaluation of the
function body encounters an explicit \texttt{return} statement. */

  configuration <T color="red">
                  <threads color="orange">
                    <thread multiplicity="*" color="yellow">
                      <k color="green"> ($PGM:K ~> execute) </k>
                      <control color="cyan">
                        <fstack color="blue"> .List </fstack>
                        <xstack color="purple"> .List </xstack>
                        <return color="LimeGreen"> void </return>
                          // holds return type
                       </control>
                      <env color="violet"> .Map </env>
                      <holds color="black"> .Map </holds>
                    </thread>
                  </threads>
//                  <br/>
                  <genv color="pink"> .Map </genv>
                  <store color="white"> .Map </store>
                  <busy color="cyan">.Set</busy>
                  <in color="magenta" stream="stdin"> .List </in>
                  <out color="brown" stream="stdout"> .List </out>
                  <nextLoc color="gray"> 0 </nextLoc>
                </T>


//@ \subsection{Declarations and Initializations}

/*@ The ``undefined'' construct is now parameterized by a type.
A main difference between untyped SIMPLE and dynamically typed SIMPLE
is that the latter assigns a type to each of its locations and that
type cannot be changed during the execution of the program.  We do not
do any memory management in our semantic definitions here, so
locations cannot be reclaimed, garbage collected and/or reused.  Each
location corresponds precisely to an allocated variable or array
element, whose type was explicitly or implicitly declared in the
program and does not change.  It is therefore safe to type each
location and then never allow that type to change.  The typed
undefined values effectively assign both a type and an undefined value
to a location. */

  syntax K ::= "undefined" "(" Type ")" [latex("\bot_{#1}")]

  rule <k> var '_:_(X:Id,, T:Type), .Exps; => . ...</k>
       <env> Env:Map => Env[L/X] </env>
       <store>... . => L |-> undefined(T) ...</store>
       <nextLoc> L:Int => L +Int 1 </nextLoc>

/*@ The dynamic semantics of typed array declarations is
similar to that in untyped SIMPLE, but we have to enforce that the
type of an array declaration be of the form \texttt{arrayOf $T$}
and assign the right type ($T$) to the allocated array locations. */

  rule <k> var '_:_(X[N:Int, (.Vals)],, arrayOf T), .Exps; => . ...</k> 
       <env> Env:Map => Env[L/X] </env>
       <store>... . => L |-> arrayRef(arrayOf T, L +Int 1, N)
                       L +Int 1 .. L +Int N |-> undefined(T) ...</store>
       <nextLoc> L:Int => L +Int 1 +Int N </nextLoc>

  context var '_:_(_[HOLE],, _),.Exps ;

/*@ The desugaring of multi-dimensional arrays into unidimensional
ones is also similar to that in untyped SIMPLE, although we have to
make sure that all the declared temporary variables have the right
types. */

  syntax Id ::= "$1" | "$2"
  rule var X[N1:Int, N2:Int, Vs:Vals] : arrayOf arrayOf T; =>
       var X[N1] : arrayOf (arrayOf T);
       {
         var ($1 : arrayOf (arrayOf T)) = X;
         for $2 = 0 to N1 - 1 do
         {
           var X[N2,Vs] : arrayOf T;
           $1[$2] = X;
         }
       }
       [structural]

/*@ Store all function parameters, as well as the return type, as part
of the lambda abstraction.  In the spirit of dynamic typing, we will
make sure that parameters are well typed when the function is invoked. */

  rule <k> function F:Id(XTs:Exps) : T:Type S:Stmt => . ...</k>
       <env> Env:Map => Env[L/F] </env>
       <store>...
         . => L |-> lambda(XTs, S, function from types(XTs) to T)
       ...</store>
       <nextLoc> L:Int => L +Int 1 </nextLoc>

/*@ \subsection{Calling \texttt{main()}}
When done with the first pass, call \texttt{main()}. */

  syntax K ::= "execute"
  rule <k> execute => String2Id("main")(.Exps); </k>
       <env> Env:Map </env>
       <genv> . => Env </genv>
       [structural]


//@ \subsection{Expressions and statements}

  rule <k> X:Id => V ...</k>
       <env>... X |-> L:Int ...</env>
       <store>... L |-> V:Val ...</store>
       [transition]

  context ++(HOLE => lvalue(HOLE))

  rule <k> ++loc(L:Int) => I +Int 1 ...</k>
       <store>... L |-> (I:Int => I +Int 1) ...</store>
       [transition]

  rule I1:Int + I2:Int => I1 +Int I2
  rule Str1:String + Str2:String => Str1 +String Str2
  rule '_-_(I1:Int,, I2:Int) => '_-Int_(I1,, I2)
  rule I1:Int * I2:Int => I1 *Int I2
  rule I1:Int / I2:Int => I1 /Int I2 when I2 =/=Int 0
  rule I1:Int % I2:Int => I1 %Int I2 when I2 =/=Int 0
  rule - I:Int => 0 -Int I
  rule I1:Int < I2:Int => I1 <Int I2
  rule I1:Int <= I2:Int => I1 <=Int I2
  rule I1:Int > I2:Int => I1 >Int I2
  rule I1:Int >= I2:Int => I1 >=Int I2
  rule V1:Val == V2:Val => V1 ==K V2
  rule V1:Val != V2:Val => V1 =/=K V2
  rule B1:Bool and B2:Bool => B1 andBool B2
  rule B1:Bool or B2:Bool => B1 orBool B2
  rule not(B:Bool) => notBool(B)

//@ Check array bounds, as part of the dynamic typing policy.

  rule V:Val[N1:Int, N2:Int, Vs:Vals] => V[N1][N2,Vs] [anywhere]

  rule arrayRef(_, L:Int, M:Int)[N:Int] => lookup(L +Int N)
       when N >=Int 0 andBool N <Int M
       [anywhere]

  rule sizeOf(arrayRef(_,_:Nat,N)) => N

//@ Define function call and return together, to see their relationship.

  syntax K ::=  "(" Map "," K "," Bag ")"

  rule <k>
         '_`(_`)(lambda(XTs:Exps, S:Stmt,
                       function from _ to T:Type),, Vs:Vals) ~> K
         =>
         bindto(XTs, Vs) ~> S ~> return;
       </k>
       <control>
         <fstack> . => ListItem((Env, K, <return> T' </return> C)) ...</fstack>
         <return> T':Type => T </return>
         C:Bag
       </control>
       <env> Env:Map => GEnv </env>
       <genv> GEnv:Map </genv>

  rule <k> return V:Val; ~> _ => V ~> K </k>
       <control>
         <fstack> ListItem((Env:Map, K:K, C:Bag)) => . ...</fstack>
         (<return> T:Type </return> _ => C)
       </control>
       <env> _ => Env </env>
       when typeOf(V) ==K T

  syntax Val ::= "nothing"

  rule return; => return nothing;   [ structural ]

  rule <k> read() => I ...</k>
       <in> ListItem(I:Int) => . ...</in>
       [transition]

  context (HOLE => lvalue(HOLE)) = _

  rule <k> loc(L:Int) = V:Val => V ...</k>
       <store>... L |-> (K:K => V) ...</store>
       when typeOf(V) ==K typeOf(K)
       [transition]

  rule {} => . [structural]

  rule <k> { Ss:Stmts } => Ss ~> env(Env) ...</k>
       <env> Env:Map </env>
       [structural]

  rule Ss1:Stmts Ss2:Stmts => Ss1 ~> Ss2  [structural]

  rule V:Val; => .

  rule if  true then S:Stmt else _ => S
  rule if false then _ else S:Stmt => S

  rule <k>
         while E:Exp do S:Stmt
         =>
         if E then {S while E do S} else {} 
       ...</k>
       [structural]

//@ We only allow printing integers and strings

  rule <k> print(V:Val, Vs:Vals => Vs);...</k>
       <out>... . => ListItem(V) </out>
       when typeOf(V) ==K int orBool typeOf(V) ==K string
      [transition]

  rule print((.Vals)); => .  [structural]

  syntax K ::= "(" Exp "," Stmt "," K "," Map "," Bag ")"

  syntax K ::= "popx"

  rule <k> (try S1:Stmt catch(X:Id) S2:Stmt => S1 ~> popx) ~> K:K </k>
       <control> 
         <xstack> . => ListItem((X,S2,K,Env,C)) ...</xstack>
         C:Bag
       </control>
       <env> Env:Map </env>

  rule <k> popx => . ...</k> 
       <xstack> _:ListItem => . ...</xstack>

  rule <k> throw V:Val; ~> _ => { var '_:_(X,, int)=V; S2 } ~> K </k>
       <control> 
         <xstack> ListItem((X:Id, S2:Stmt, K:K, Env:Map, C:Bag))
                  =>
                  .
         ...</xstack>
         (_ => C)
       </control>
       <env> _ => Env </env>

   rule <thread>... 
          <k> spawn S:Stmt => . ...</k>
          <env> Env:Map </env>
        ...</thread>
        (. => <thread>... <k> S </k> <env> Env </env> ...</thread>)

   rule (<thread>... <k> .K </k> <holds> H:Map </holds> ...</thread> => .)
        <busy> Busy:Set => Busy -Set keys(H) </busy>

   rule <k> acquire V:Val; => . ...</k>
        <holds>... . => V |-> 0 ...</holds>
        <busy> Busy:Set (. => SetItem(V)) </busy>
        when notBool(V in Busy)
        [transition]

   rule <k> acquire V:Val; => . ...</k>
        <holds>...V |-> (N:Int => N +Int 1) ...</holds>

   rule <k> release V:Val; => . ...</k>
        <holds>... V:Val |-> (N:Int => N -Int 1) ...</holds>
     when N >Int 0

   rule <k> release V:Val; => . ...</k>
        <holds>... V |-> 0 => . ...</holds>
        <busy>... SetItem(V) => . ...</busy>

   rule <k> rendezvous V:Val; => . ...</k>
        <k> rendezvous V; => . ...</k> [transition]

//@ \subsection{Auxiliary operations}

//@ \texttt{lvalue}
  syntax Exp ::= "lvalue" "(" K ")"

  syntax Val ::= "loc" "(" Int ")"

  rule <k> lvalue(X:Id) => loc(L:Int) ...</k>
       <env>... X |-> L:Int ...</env>
       [structural]

  context lvalue(_[HOLE])
  context lvalue(HOLE[_])

  rule <k> lvalue(lookup(L:Int)) => loc(L) ...</k>  [structural]

//@ \texttt{lookup}

  syntax K ::= "lookup" "(" Int ")"

  rule <k> lookup(L:Int) => V ...</k>
       <store>... L |-> V:Val ...</store>
       [transition]

//@ \texttt{bindto} also checks the well-formedness of the function parameters

  syntax K ::= "bindto" "(" Exps "," Vals ")"

  rule <k> bindto(('_:_(X,, T), XTs:Exps => XTs),
                  (V:Val, Vs:Vals => Vs))
       ...</k>
       <env> Env:Map => Env[L/X] </env>
       <store>... . => L |-> V ...</store>
       <nextLoc> L:Int => L +Int 1 </nextLoc>
       when typeOf(V) ==K T

  rule <k> bindto(.Exps,.Vals) => . ...</k>  [structural]

//@ \texttt{env}

  syntax K ::= "env" "(" Map ")"

  rule <k> env(Env:Map) => . ...</k>
       <env> _ => Env </env>
       [structural]

  rule (env(_) => .) ~> env(_) [structural]

//@ \texttt{typeOf}

  syntax Type ::= "typeOf" "(" K ")"   [function, klabel(typeOf)]

  rule typeOf(_:Int) => int        [anywhere]
  rule typeOf(_:Bool) => bool      [anywhere]
  rule typeOf(_:String) => string  [anywhere]

  rule typeOf(arrayRef(T:Type ,_:Int,_:Int)) => T  [anywhere]
  rule typeOf(lambda(_, _, T:Type)) => T           [anywhere]

  rule typeOf(undefined(T:Type)) => T  [anywhere]
  rule typeOf(nothing) => void         [anywhere]

/*@ Recall that lists of the form "a,b,c" are a syntactic convenience,
which eventually are translated into cons-lists "(a,(b,(c,.)))".
Unfortunately, the current K tool is not able to cons-listify
the RHSes of the rules below, so we have to do it manually.  */

  syntax Types ::= "types" "(" Exps ")"   [function, klabel(types)]

  rule types(.Exps) => void, .Types  [anywhere]
  rule types('_:_(X:Id,, T:Type), .Exps) => T,.Types  [anywhere]
  rule types('_:_(X:Id,, T:Type), (E:Exp, Es:Exps))
        => 
       (T, types(E,Es))
       [anywhere]


//@ Sequences of locations

  syntax List{K} ::= Int ".." Int
  rule N1:Int..N2:Int => .List{K}              when N1  >Int N2 [anywhere]
  rule N1:Int..N2:Int => N1 ,, (N1 +Int 1)..N2 when N1 <=Int N2 [anywhere]

endmodule
