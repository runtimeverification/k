// Copyright (c) 2014 K Team. All Rights Reserved.
/*!
\title{SIMPLE --- Typed --- Dynamic}
\author{Grigore Ro\c{s}u and Traian Florin \c{S}erb\u{a}nu\c{t}\u{a}
        (\texttt{\{grosu,tserban2\}@illinois.edu})}
\organization{University of Illinois at Urbana-Champaign}
*/

/*@ \section{Abstract}
This is the \K dynamic semantics of the typed SIMPLE language.
It is very similar to the semantics of the untyped SIMPLE, the
difference being that we now dynamically check the typing policy
described in the static semantics of typed SIMPLE.  Because of the
dynamic nature of the semantics, we can also perform some additional
checks which were not possible in the static semantics, such as
memory leaks due to accessing an array out of its bounds.  We will
highlight the differences between the dynamically typed and the
untyped SIMPLE as we proceed with the semantics.  We recommend the
reader to consult the typing policy and the syntax of types discussed
in the static semantics of the typed SIMPLE language. */

module SIMPLE-TYPED-DYNAMIC-SYNTAX

/*@ \section{Syntax}
The syntax of typed SIMPLE extends that of untyped SIMPLE with support
for declaring types to variables and functions. */

/*@ The syntax below is identical to that of the static semantics of typed
SIMPLE.  However, the \K strictness attributes are like those of the untyped
SIMPLE, to capture the desired evaluation strategies of the various language
constructs. */

  syntax Id ::= Token{"main"}

//@ \subsection{Types}

  syntax Type ::= "void" | "int" | "bool" | "string"
                | Type "[" "]"
                > Types "->" Type
                | "(" Type ")"           [bracket]
  syntax Types ::= List{Type,","}

//@ \subsection{Declarations}

  syntax Param ::= Type Id
  syntax Params ::= List{Param,","}

  syntax Decl ::= Type Exps ";"
                | Type Id "(" Params ")" Block

//@ \subsection{Expressions}

  syntax Exp ::= Int | Bool | String | Id
               | "(" Exp ")"             [bracket]
               | "++" Exp
               > Exp "[" Exps "]"        [strict, klabel("'_:Exp[_:Exps]")]
               > Exp "(" Exps ")"        [strict]
               | "-" Exp                 [strict]
               | "sizeOf" "(" Exp ")"    [strict]
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
               > "!" Exp                 [strict]
               > left:
                 Exp "&&" Exp            [strict(1), left]
               | Exp "||" Exp            [strict(1), left]
               > "spawn" Block
               > Exp "=" Exp             [strict(2), right]

/*@ Like in the static semantics, there is no need for lists of identifiers
(because we now have lists of parameters). */

  syntax Exps ::= List{Exp,","}          [strict]

//@ \subsection{Statements}

  syntax Block ::= "{" "}"
                | "{" Stmts "}"

  syntax Stmt ::= Decl | Block
                | Exp ";"                               [strict]
                | "if" "(" Exp ")" Block "else" Block   [avoid, strict(1)]
                | "if" "(" Exp ")" Block
                | "while" "(" Exp ")" Block
                //| "for" "(" Stmt Exp ";" Exp ")" Block
                   | "for" "(" Stmts Exp ";" Exp ")" Block
                | "print" "(" Exps ")" ";"              [strict]
                | "return" Exp ";"                      [strict]
                | "return" ";"
                | "try" Block "catch" "(" Param ")" Block
                | "throw" Exp ";"                       [strict]
                | "join" Exp ";"                        [strict]
                | "acquire" Exp ";"                     [strict]
                | "release" Exp ";"                     [strict]
                | "rendezvous" Exp ";"                  [strict]

  syntax Stmts ::= Stmt
                 | Stmts Stmts                          [right]

/*@ The same desugaring macros like in the statically typed SIMPLE. */

  rule if (E) S => if (E) S else {}                                     [macro]
  rule for(Start Cond; Step) {S:Stmts} => {Start while(Cond){S Step;}}  [macro]
  rule for(Start Cond; Step) {} => {Start while(Cond){Step;}}           [macro]
  rule T:Type E1:Exp, E2:Exp, Es:Exps; => T E1; T E2, Es;               [macro]
  rule T:Type X:Id = E; => T X; X = E;                                  [macro]

endmodule


module SIMPLE-TYPED-DYNAMIC
  imports SIMPLE-TYPED-DYNAMIC-SYNTAX

//@ \section{Semantics}

/*@ \subsection{Values and results}
These are similar to those of untyped SIMPLE, except that the array
references and the function abstrations now also hold their types.
These types are needed in order to easily compute the type of any
value in the language (see the auxiliary \texttt{typeOf} operation at
the end of this module). */

  syntax Val ::= Int | Bool | String
               | array(Type,Int,Int)
               | lambda(Type,Params,Stmts)
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
                      <k color="green"> ($PGM:Stmts ~> execute) </k>
                      <br/>
                      <control color="cyan">
                        <fstack color="blue"> .List </fstack>
                        <xstack color="purple"> .List </xstack>
                        <return color="LimeGreen"> void </return> //return type
                       </control>
                      <br/>
                      <env color="violet"> .Map </env>
                      <holds color="black"> .Map </holds>
                      <id color="pink"> 0 </id>
                    </thread>
                  </threads>
                  <br/>
                  <genv color="pink"> .Map </genv>
                  <store color="white"> .Map </store>
                  <busy color="cyan">.Set</busy>
                  <terminated color="red"> .Set </terminated>
                  <in color="magenta" stream="stdin"> .List </in>
                  <out color="brown" stream="stdout"> .List </out>
                  <nextLoc color="gray"> 0 </nextLoc>
                </T>

//@ \subsection{Declarations and Initialization}

/*@ \subsubsection{Variable Declaration}
The ``undefined'' construct is now parameterized by a type.
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

  syntax KItem ::= undefined(Type)  [latex(\bot_{#1})]

  rule <k> T:Type X:Id; => . ...</k>
       <env> Env => Env[X <- L] </env>
       <store>... .Map => L |-> undefined(T) ...</store>
       <nextLoc> L:Int => L +Int 1 </nextLoc>

/*@ \subsubsection{Array Declaration}
The dynamic semantics of typed array declarations is similar to that
in untyped SIMPLE, but we have to make sure that we associate the
right type to the allocated locations. */

  rule <k> T:Type X:Id[N:Int]; => . ...</k>
       <env> Env => Env[X <- L] </env>
       <store>... .Map => L |-> array(T, L +Int 1, N)
                       (L +Int 1)...(L +Int N) |-> undefined(T) ...</store>
       <nextLoc> L:Int => L +Int 1 +Int N </nextLoc>
    when N >=Int 0

  context _:Type _:>Exp[HOLE:>Exps];

/*@ The desugaring of multi-dimensional arrays into unidimensional
ones is also similar to that in untyped SIMPLE, although we have to
make sure that all the declared variables have the right types.  The
auxiliary operation \texttt{T<Vs>}, defined at the end of the file,
adds the length of \texttt{Vs} dimensions to the type \texttt{T}. */

  syntax Id ::= Token{"$1"} | Token{"$2"}
  rule T:Type X:Id[N1:Int, N2:Int, Vs:Vals];
    => T[]<Vs> X[N1];
       {
         T[][]<Vs> $1=X;
         for(int $2=0; $2 <= N1 - 1; ++$2) {
           T X[N2,Vs];
           $1[$2] = X;
         }
       }
    [structural]

/*@ \subsubsection{Function declaration}
Store all function parameters, as well as the return type, as part
of the lambda abstraction.  In the spirit of dynamic typing, we will
make sure that parameters are well typed when the function is invoked. */

  rule <k> T:Type F:Id(Ps:Params) S => . ...</k>
       <env> Env => Env[F <- L] </env>
       <store>... .Map => L |-> lambda(T, Ps, S) ...</store>
       <nextLoc> L => L +Int 1 </nextLoc>

/*@ \subsection{Calling \texttt{main()}}
When done with the first pass, call \texttt{main()}. */

  syntax KItem ::= "execute"
  rule <k> execute => main(.Exps); </k>
       <env> Env </env>
       <genv> .Map => Env </genv>  [structural]

//@ \subsection{Expressions}

//@ \subsubsection{Variable lookup}

  rule <k> X:Id => V ...</k>
       <env>... X |-> L ...</env>
       <store>... L |-> V:Val ...</store>  [lookup]

//@ \subsubsection{Variable/Array increment}

  context ++(HOLE => lvalue(HOLE))
  rule <k> ++loc(L) => I +Int 1 ...</k>
       <store>... L |-> (I:Int => I +Int 1) ...</store>  [increment]

//@ \subsubsection{Arithmetic operators}

  rule I1:Int + I2:Int => I1 +Int I2
  rule Str1:String + Str2:String => Str1 +String Str2
  rule I1:Int - I2:Int => I1 -Int I2
  rule I1:Int * I2:Int => I1 *Int I2
  rule I1:Int / I2:Int => I1 /Int I2 when I2 =/=K 0
  rule I1:Int % I2:Int => I1 %Int I2 when I2 =/=K 0
  rule - I:Int => 0 -Int I
  rule I1:Int < I2:Int => I1 <Int I2
  rule I1:Int <= I2:Int => I1 <=Int I2
  rule I1:Int > I2:Int => I1 >Int I2
  rule I1:Int >= I2:Int => I1 >=Int I2
  rule V1:Val == V2:Val => V1 ==K V2
  rule V1:Val != V2:Val => V1 =/=K V2
  rule ! T:Bool => notBool(T)
  rule true  && E => E
  rule false && _ => false
  rule true  || _ => true
  rule false || E => E

/*@ \subsubsection{Array lookup}

Check array bounds, as part of the dynamic typing policy. */

  rule V:Val[N1:Int, N2:Int, Vs:Vals] => V[N1][N2, Vs]
    [structural, anywhere]

  rule array(_:Type, L:Int, M:Int)[N:Int] => lookup(L +Int N)
    when N >=Int 0 andBool N <Int M  [structural, anywhere]

//@ \subsubsection{Size of an array}

  rule sizeOf(array(_,_,N)) => N

/*@ \subsubsection{Function call}

Define function call and return together, to see their relationship.
Note that the operation \texttt{mkDecls} now declares properly typed
instantiated variables, and that the semantics of \texttt{return} also
checks that that type of the returned value is expected one. */

  syntax KItem ::= (Type,Map,K,ControlCellFragment)

  rule <k> lambda(T,Ps,S)(Vs:Vals) ~> K => mkDecls(Ps,Vs) S return; </k>
       <control>
         <fstack> .List => ListItem((T',Env,K,C)) ...</fstack>
         <return> T' => T </return>
         C
       </control>
       <env> Env => GEnv </env>
       <genv> GEnv </genv>

  rule <k> return V:Val; ~> _ => V ~> K </k>
       <control>
         <fstack> ListItem((T',Env,K,C)) => .List ...</fstack>
         <return> T => T' </return>
         (_ => C)
       </control>
       <env> _ => Env </env>
    when typeOf(V) ==K T   // check the type of the returned value

/*@ Like the \texttt{undefined} above, \texttt{nothing} also gets
tagged with a type now.  The empty \texttt{return} statement is
completed to return the \texttt{nothing} value tagged as expected. */

  syntax Val ::= nothing(Type)
  rule <k> return; => return nothing(T); ...</k> <return> T </return>
    [structural]

//@ \subsubsection{Read}

  rule <k> read() => I ...</k> <in> ListItem(I:Int) => .List ...</in>  [read]

/*@ \subsubsection{Assignment}
The assignment now checks that the type of the assigned location is
preserved: */

  context (HOLE => lvalue(HOLE)) = _

  rule <k> loc(L) = V:Val => V ...</k> <store>... L |-> (V' => V) ...</store>
    when typeOf(V) ==K typeOf(V')  [assignment]

//@ \subsection{Statements}

//@ \subsubsection{Blocks}

  rule {} => .  [structural]
  rule <k> { S } => S ~> env(Env) ...</k>  <env> Env </env>  [structural]

//@ \subsubsection{Sequential composition}

  rule S1:Stmts S2:Stmts => S1 ~> S2  [structural]

//@ \subsubsection{Expression statements}

  rule _:Val; => .

//@ \subsubsection{Conditional}

  rule if ( true) S else _ => S
  rule if (false) _ else S => S

//@ \subsubsection{While loop}

  rule while (E) S => if (E) {S while(E)S}  [structural]

/*@ \subsubsection{Print}

We only allow printing integers and strings: */

  rule <k> print(V:Val, Es => Es); ...</k> <out>... .List => ListItem(V) </out>
    when typeOf(V) ==K int orBool typeOf(V) ==K string  [print]
  rule print(.Vals); => .  [structural]

/*@ \subsubsection{Exceptions}

Exception parameters are now typed, but note that the semantics below
works correctly only when the thrown exception has the same type as
the innermost try-catch paramete.  To keep things simple, for the time
being we can assume that SIMPLE only throws and catches integer
values, in which case our semantics below works fine: */

  syntax KItem ::= (Param,Stmt,K,Map,ControlCellFragment)  // Param instead of Id

  syntax KItem ::= "popx"

  rule <k> (try S1 catch(P) S2 => S1 ~> popx) ~> K </k>
       <control>
         <xstack> .List => ListItem((P, S2, K, Env, C)) ...</xstack>
         C
       </control>
       <env> Env </env>

  rule <k> popx => . ...</k>
       <xstack> ListItem(_) => .List ...</xstack>

  rule <k> throw V:Val; ~> _ => { T X = V; S2 } ~> K </k>
       <control>
         <xstack> ListItem((T:Type X:Id, S2, K, Env, C)) => .List ...</xstack>
         (_ => C)
       </control>
       <env> _ => Env </env>

//@ \subsubsection{Threads}

//@ {Thread creation}

   rule <thread>...
          <k> spawn S => !T:Int ...</k>
          <env> Env </env>
        ...</thread>
        (. => <thread>...
                <k> S </k>
                <env> Env </env>
                <id> !T </id>
              ...</thread>)

//@ {Thread termination}

   rule (<thread>... <k>.</k> <holds>H</holds> <id>T</id> ...</thread> => .)
        <busy> Busy => Busy -Set keys(H) </busy>
        <terminated>... .Set => SetItem(T) ...</terminated>

//@ {Thread joining}

   rule <k> join T:Int; => . ...</k>
        <terminated>... SetItem(T) ...</terminated>

//@ {Acquire lock}

   rule <k> acquire V:Val; => . ...</k>
        <holds>... .Map => V |-> 0 ...</holds>
        <busy> Busy (.Set => SetItem(V)) </busy>
     when (notBool(V in Busy:Set))  [acquire]

   rule <k> acquire V; => . ...</k>
        <holds>... V:Val |-> (N:Int => N +Int 1) ...</holds>

//@ {Release lock}

   rule <k> release V:Val; => . ...</k>
        <holds>... V |-> (N => N:Int -Int 1) ...</holds>
      when N >Int 0

   rule <k> release V; => . ...</k> <holds>... V:Val |-> 0 => .Map ...</holds>
        <busy>... SetItem(V) => .Set ...</busy>

//@ {Rendezvous synchronization}

   rule <k> rendezvous V:Val; => . ...</k>
        <k> rendezvous V; => . ...</k>  [rendezvous]

//@ \subsection{Auxiliary declarations and operations}

/*@ Turns a list of parameters and a list of instance values for them
into a list of variable declarations. */
  syntax Stmts ::= mkDecls(Params,Vals)  [function]
  rule mkDecls((T:Type X:Id, Ps:Params), (V:Val, Vs:Vals))
    => T X=V; mkDecls(Ps,Vs)
  rule mkDecls(.Params,.Vals) => {}

//@ Location lookup.

  syntax KItem ::= lookup(Int)
  rule <k> lookup(L) => V ...</k> <store>... L |-> V:Val ...</store>  [lookup]

//@ Environment recovery.

  syntax KItem ::= env(Map)
  rule <k> env(Env) => . ...</k>  <env> _ => Env </env>  [structural]
  rule (env(_) => .) ~> env(_)  [structural]

//@ lvalue and loc

  syntax Exp ::= lvalue(K)
  syntax Val ::= loc(Int)

  rule <k> lvalue(X:Id => loc(L)) ...</k>  <env>... X |-> L:Int ...</env>
    [structural]

  //context lvalue(_[HOLE])
  //context lvalue(HOLE[_])
  context lvalue(_:>Exp[HOLE:>Exps])
  context lvalue(HOLE:>Exp[_:>Exps])

  rule lvalue(lookup(L:Int) => loc(L))  [structural]

/*@ Adds the corresponding depth to an array type */

  syntax Type ::= Type "<" Vals ">"  [function]
  rule T:Type<_,Vs:Vals> => T[]<Vs>
  rule T:Type<.Vals> => T

//@ Sequences of locations.
  syntax Map ::= Int "..." Int "|->" K
    [function, latex({#1}\ldots{#2}\mapsto{#3})]
  rule N...M |-> _ => .Map  when N >Int M
  rule N...M |-> K => N |-> K (N +Int 1)...M |-> K  when N <=Int M

// Type of a value.
  syntax Type ::= typeOf(K)  [function]
  rule typeOf(_:Int) => int
  rule typeOf(_:Bool) => bool
  rule typeOf(_:String) => string
  rule typeOf(array(T,_,_)) => (T[])   // () needed! K parses [] as "no tags"
  rule typeOf(lambda(T,Ps,_)) => getTypes(Ps) -> T
  rule typeOf(undefined(T)) => T
  rule typeOf(nothing(T)) => T

//@ List of types of a parameter.
  syntax Types ::= getTypes(Params)  [function]
  rule getTypes(T:Type _:Id) => T, .Types   // I would like to not use .Types
  rule getTypes(T:Type _:Id, P, Ps) => T, getTypes(P,Ps)
  rule getTypes(.Params) => void, .Types
endmodule
