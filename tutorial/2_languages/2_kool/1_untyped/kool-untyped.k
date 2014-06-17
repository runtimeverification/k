// Copyright (c) 2012-2014 K Team. All Rights Reserved.
/*!
\title{KOOL --- Untyped}
\author{Grigore Ro\c{s}u and Traian Florin \c{S}erb\u{a}nu\c{t}\u{a}
        (\texttt{\{grosu,tserban2\}@illinois.edu})}
\organization{University of Illinois at Urbana-Champaign}
*/

/*@
\section{Abstract}
This is the \K semantic definition of the untyped KOOL language.  KOOL
is aimed at being a pedagogical and research language that captures
the essence of the object-oriented programming paradigm.  Its untyped
variant discussed here is simpler than the typed one, ignoring several
intricate aspects of types in the presence of objects.  A program
consists of a set of class declarations.  Each class can extend at
most one other class (KOOL is single-inheritance).  A class can
declare a set of fields and a set of methods, all public and called
the class' \textit{members}.  Specifically, KOOL includes the
following features:
\begin{itemize}
\item Class declarations, where a class may or may not explicitly
extend another class.  In case a class does not explicitly extend
another class, then it is assumed that it extends the default top-most
and empty (i.e., no members) class called \texttt{Object}.  Each class
is required to declare precisely one homonymous method, called its
\textit{constructor}.  Each valid program should contain one class
named \texttt{Main}, whose constructor, \texttt{Main()}, takes no
arguments.  The execution of a program consists of creating an object
instance of class \texttt{Main} and invoking the constructor
\texttt{Main()} on it, that is, of executing ``\texttt{new Main();}''.
\item All features of SIMPLE (see {\texttt{examples/simple/untyped}}),
i.e., multidimensional arrays, function (here called ``method'')
abstractions with call-by-value parameter passing style and static
scoping, blocks with locals, input/output, parametric exceptions, and
concurrency via dynamic thread creation/termination and synchronization.
The only change in the syntax of SIMPLE when imported in KOOL is the
function declaration keyword, \texttt{function}, which is changed into
\texttt{method}.  The exact same desugaring macros from SIMPLE are
also included in KOOL.  We can think of KOOL's classes as embedding
SIMPLE programs (extended with OO constructs, as discussed next).
\item Object creation using the ``\texttt{new C(e1,...,en)}''
expression construct.  An object instance of class \texttt{C} is first
created and then the constructor \texttt{C(e1,...,en)} is implicitly
called on that object.  KOOL only allows (and requires) one
constructor per class.  The class constructor can be called either
implicitly during a new object creation for the class, or explicitly.
The superclass constructor is {\em not} implicitly invoked when a
class constructor is invoked; if you want to invoke the superclass
constructor from a subclass constructor then you have to do it
explicitly.
\item An expression construct \texttt{this}, which evaluates to the
current object.
\item An expression construct \texttt{super}, which is used (only) in
combination with member lookup (see next) to refer to a superclass
field or method.
\item A member lookup expression construct \texttt{e.x}, where \texttt{e}
is an expression (either an expression expected to evaluate to an object
or the \texttt{super} construct) and \texttt{x} is a class member name,
that is, a field or a method name.
\item Expression constructs ``\texttt{e instanceOf C}'' and
``\texttt{(C) e}'', where \texttt{e} is an expression expected
to evaluate to an object and \texttt{C} a class name.  The former
tells whether the class of \texttt{e} is a subclass of \texttt{C},
that is, whether \texttt{e} can be used as an instance of \texttt{C},
and the latter changes the class of \texttt{e} to \texttt{C}.  These
operations always succeed: the former returns a Boolean value, while
the latter changes the current class of \texttt{e} to \texttt{C}
regardless of whether it is safe to do so or not.  The typed version
of KOOL will check the safety of casting by ensuring that the instance
class of the object is a subclass of \texttt{C}.  In untyped KOOL we
do not want to perform this check because we want to allow the
programmer maximum of flexibility: if one always accesses only
available members, then the program can execute successfully despite
the potentially unsafe cast.
\end{itemize}

There are some specific aspects of KOOL that need to be discussed.

First, KOOL is higher-order, allowing function abstractions to be
treated like any other values in the language.  For example, if
\texttt{m} is a method of object \texttt{e} then \texttt{e.m}
evaluates to the corresponding function abstraction.  The function
abstraction is in fact a closure, because in addition to the method
parameters and body it also encapsulates the object value (i.e., the
environment of the object together with its current class---see below)
that \texttt{e} evaluates to.  This way, function abstractions can be
invoked anywhere and have the capability to change the state of their
object.  For example, if \texttt{m} is a method of object \texttt{e}
which increments a field \texttt{c} of \texttt{e} when invoked, and if
\texttt{getm} is another method of \texttt{e} which simply returns
\texttt{m} when invoked, then the double application
\texttt{(e.getm())()} has the same effect as \texttt{e.m()}, that is,
increments the counter \texttt{c} of \texttt{e}.  Note that the
higher-order nature of KOOL was not originally planned; it came as a
natural consequence of evaluating methods to closures and we decided
to keep it.  If you do not like it then do not use it.

Second, since all the fields and methods are public in KOOL and since
they can be redeclared in subclasses, it is not immediately clear how
to lookup the member \texttt{x} when we write \texttt{e.x} and
\texttt{e} is different from \texttt{super}.  We distinguish two cases,
depending on whether \texttt{e.x} occurs in a method invocation
context (i.e., \texttt{e.x(...)}) or in a field context.  KOOL has
dynamic method dispatch, so if \texttt{e.x} is invoked as a method
then \texttt{x} will be searched for starting with the instance class of
the object value to which \texttt{e} evaluates.  If \texttt{e.x}
occurs in a non-method-invocation context then \texttt{x} will be
treated as a field (although it may hold a method closure due to the
higher-order nature of KOOL) and thus will be searched starting with
the current class of the object value of \texttt{e} (which, because of
\texttt{this} and casting, may be different from its instance class).
In order to achieve the above, each object value will consist of a
pair holding the current class of the object and an environment stack
with one layer for each class in the object's instance class hierarchy.

Third, although KOOL is dynamic method dispatch, its capabilities
described above are powerful enough to allow us to mimic static
method dispatch.  For example, suppose that you want to invoke method
\texttt{m()} statically.  Then all you need to do is to declare a
local variable and bind it to \texttt{m}, for example ``\texttt{var
staticm = m;}'', and then call \texttt{staticm()}.  This works because
\texttt{staticm} is first bound to the method closure that \texttt{m}
evaluates to, and then looked up as any local variable when invoked.
We only enable the dynamic method dispatch when we have an object
member on an application position, e.g., \texttt{m()}.

In what follows, we limit our comments to the new, KOOL-specific
aspects of the language.  We refer the reader to the untyped SIMPLE
language for documentation on the the remaining features, because
those were all borrowed from SIMPLE. */

module KOOL-UNTYPED-SYNTAX
  imports BUILTIN-SYNTAX-HOOKS

/*@ \section{Syntax}

The syntax of KOOL extends that of SIMPLE with object-oriented
constructs.  We removed from the \K annotated syntax of SIMPLE two
constructs, namely the one for function declarations (because we want
to call them ``methods'' now) and the one for function application
(because application is not strict in the first argument
anymore---needs to initiate dynamic method dispatch).  The additional
syntax includes:
\begin{itemize}
\item First, we need a new dedicated identifier, \texttt{Object}, for
the default top-most class.
\item Second, we rename the \texttt{function} keyword of SIMPLE into
\texttt{method}.
\item Third, we add syntax for class declarations together with a
macro making classes which extend nothing to extend \texttt{Object}.
\item Fourth, we change the strictness attribute of application
into \texttt{strict(2)}.
\item Finally, we add syntax and corresponding strictness
for the KOOL object-oriented constructs.
\end{itemize} */

  syntax Id ::= "Object" | "Main"

  syntax Decl ::= "var" Exps ";"
                | "method" Id "(" Ids ")" Block  // called "function" in SIMPLE
                | "class" Id Block               // KOOL
                | "class" Id "extends" Id Block  // KOOL

  syntax Exp ::= Int | Bool | String | Id
               | "this"                                 // KOOL
               | "super"                                // KOOL
               | "(" Exp ")"             [bracket]
               | "++" Exp
               | Exp "instanceOf" Id     [strict(1)]    // KOOL
               | "(" Id ")" Exp          [strict(2)]    // KOOL  cast
               | "new" Id "(" Exps ")"   [strict(2)]    // KOOL
               | Exp "." Id                             // KOOL
               > Exp "[" Exps "]"        [strict]
               > Exp "(" Exps ")"        [strict(2)]    // was strict in SIMPLE
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

  syntax Ids  ::= List{Id,","}
  syntax Exps ::= List{Exp,","}          [strict]


  syntax Block ::= "{" "}"
                | "{" Stmts "}"

  syntax Stmt ::= Decl | Block
                | Exp ";"                               [strict]
                | "if" "(" Exp ")" Block "else" Block   [avoid, strict(1)]
                | "if" "(" Exp ")" Block
                | "while" "(" Exp ")" Block
        	| "for" "(" Stmts Exp ";" Exp ")" Block
                | "return" Exp ";"                      [strict]
                | "return" ";"
                | "print" "(" Exps ")" ";"              [strict]
                | "try" Block "catch" "(" Id ")" Block
                | "throw" Exp ";"                       [strict]
                | "join" Exp ";"                        [strict]
                | "acquire" Exp ";"                     [strict]
                | "release" Exp ";"                     [strict]
                | "rendezvous" Exp ";"                  [strict]

  syntax Stmts ::= Stmt
                 | Stmts Stmts                          [right]



//@ Old desugaring rules, from SIMPLE

  rule if (E) S => if (E) S else {}                                 [macro]
  rule for(Start Cond; Step) {S} => {Start while (Cond) {S Step;}}  [macro]
  rule var E1:Exp, E2:Exp, Es:Exps; => var E1; var E2, Es;          [macro]
  rule var X:Id = E; => var X; X = E;                               [macro]

//@ New desugaring rule

  rule class C:Id S => class C extends Object S                     // KOOL

endmodule

/*@ \section{Semantics}

We first discuss the new configuration of KOOL, which extends that of
SIMPLE.  Then we include the semantics of the constructs borrowed from
SIMPLE unchanged; we refrain from discussing those, because they were
already discussed in the \K definition of SIMPLE.  Then we discuss
changes to SIMPLE's semantics needed for the more general meaning of
the previous SIMPLE constructs (for example for thread spawning,
assignment, etc.).  Finally, we discuss in detail the
semantics of the additional KOOL constructs. */

module KOOL-UNTYPED
  imports KOOL-UNTYPED-SYNTAX

/*@ \subsection{Configuration}

KOOL removes one cell and adds two nested cells to the configuration
of SIMPLE.  The cell which is removed is the one holding the global
environment, because a KOOL program consists of a set of classes only,
with no global declarations.  In fact, since informally speaking each
KOOL class now includes a SIMPLE program, it is safe to say that the
global variables in SIMPLE became class fields in KOOL.  Let us now
discuss the new cells that are added to the configuration of SIMPLE.
\begin{itemize}
\item The cell \textsf{crntObj} holds data pertaining to the current
object, that is, the object environment in which the code in cell
\textsf{k} executes: \textsf{crntClass} holds the current class (which
can change as methods of the current object are invoked);
\textsf{envStack} holds the stack of environments as a list,
each layer corresponding to one class in the objects' instance class
hierarchy; \textsf{location}, which is optional, holds the location in
the store where the current object is or has to be located (this is
useful both for method closures and for the semantics of object
creation).
\item The cell \textsf{classes} holds all the declared classes, each
class being held in its own \textsf{class} cell which contains a name
(\textsf{className}), a parent (\textsf{extends}), and the actual
member declarations (\textsf{declarations}).
\end{itemize}
*/

  configuration <T color="red">
                  <threads color="orange">
                    <thread multiplicity="*" color="yellow">
                      <k color="green"> ($PGM:Stmts ~> execute) </k>
                      <br/>
                      <control color="cyan">
                        <fstack color="blue"> .List </fstack>
                        <xstack color="purple"> .List </xstack>
                        <br/>
                        <crntObj color="Fuchsia">  // KOOL
                           <crntClass> Object </crntClass>
                           <envStack> .List </envStack>
                           <location multiplicity="?"> .K </location>
                        </crntObj>
                      </control>
                      <br/>
                      <env color="violet"> .Map </env>
                      <holds color="black"> .Map </holds>
                      <id color="pink"> 0 </id>
                    </thread>
                  </threads>
                  <br/>
                  <store color="white"> .Map </store>
                  <busy color="cyan">.Set </busy>
                  <terminated color="red"> .Set </terminated>
                  <in color="magenta" stream="stdin"> .List </in>
                  <out color="brown" stream="stdout"> .List </out>
                  <nextLoc color="gray"> 0 </nextLoc>
                  <br/>
                  <classes color="Fuchsia">        // KOOL
                     <class multiplicity="*" color="Fuchsia">
                        <className color="Fuchsia"> Main </className>
                        <extends color="Fuchsia"> Object </extends>
                        <declarations color="Fuchsia"> .K </declarations>
                     </class>
                  </classes>
                </T>

/*@ \subsection{Unchanged Semantics from untyped SIMPLE}

The semantics below is taken over from SIMPLE unchanged.
The semantics of function declaration and invocation, including the
use of the special \texttt{lambda} abstraction value, needs to change
in order to account for the fact that methods are now invoked into
their object's environment.  The semantics of function return actually
stays unchanged.  Also, the semantics of program initialization is
different: now we have to create an instance of the \texttt{Main}
class which also calls the constructor \texttt{Main()}, while in
SIMPLE we only had to invoke the function \texttt{Main()}.
Finally, the semantics of thread spawning needs to change, too: the
parent thread needs to also share its object environment with the
spawned thread (in addition to its local environment, like in SIMPLE).
This is needed in order to be able to spawn method invokations under
dynamic method dispatch; for example, ``\texttt{spawn \{ run(); \}}''
will need to look up the method \texttt{run()} in the newly created
thread, operation which will most likely fail unless the child thread
sees the object environment of the parent thread.  Note that the
\texttt{spawn} statement of KOOL is more permissive than the threads
of Java.  In fact, the latter can be implemented in terms of our
\texttt{spawn}---see the program \texttt{threads.kool} for a sketch.  */

/*@ Below is a subset of the values of SIMPLE, which are also values
of KOOL.  We will add other values later in the semantics, such as
object and method closures. */

  syntax Val ::= Int | Bool | String
               | array(Int,Int)
  syntax Vals ::= List{Val,","}
  syntax Exp ::= Val
  syntax KResult ::= Val

/*@ The semantics below are taken verbatim from the untyped SIMPLE
definition. */

  syntax KItem ::= "undefined"  [latex(\bot)]

  rule <k> var X:Id; => . ...</k>
       <env> Env => Env[X <- L] </env>
       <store>... .Map => L |-> undefined ...</store>
       <nextLoc> L:Int => L +Int 1 </nextLoc>


  context var _:Id[HOLE];

  rule <k> var X:Id[N:Int]; => . ...</k>
       <env> Env => Env[X <- L] </env>
       <store>... .Map => L |-> array(L +Int 1, N)
                          (L +Int 1) ... (L +Int N) |-> undefined ...</store>
       <nextLoc> L:Int => L +Int 1 +Int N </nextLoc>
    when N >=Int 0


  syntax Id ::= "$1" | "$2"
  rule var X:Id[N1:Int, N2:Int, Vs:Vals];
    => var X[N1];
       {
         var $1=X;
         for(var $2=0; $2 <= N1 - 1; ++$2) {
           var X[N2,Vs];
           $1[$2] = X;
         }
       }
    [structural]


  rule <k> X:Id => V ...</k>
       <env>... X |-> L ...</env>
       <store>... L |-> V:Val ...</store>  [lookup]


  context ++(HOLE => lvalue(HOLE))
  rule <k> ++loc(L) => I +Int 1 ...</k>
       <store>... L |-> (I:Int => I +Int 1) ...</store>  [increment]


  rule I1 + I2 => I1 +Int I2
  rule Str1 + Str2 => Str1 +String Str2
  rule I1 - I2 => I1 -Int I2
  rule I1 * I2 => I1 *Int I2
  rule I1 / I2 => I1 /Int I2 when I2 =/=K 0
  rule I1 % I2 => I1 %Int I2 when I2 =/=K 0
  rule - I => 0 -Int I
  rule I1 < I2 => I1 <Int I2
  rule I1 <= I2 => I1 <=Int I2
  rule I1 > I2 => I1 >Int I2
  rule I1 >= I2 => I1 >=Int I2

  rule V1:Val == V2:Val => V1 ==K V2
  rule V1:Val != V2:Val => V1 =/=K V2
  rule ! T => notBool(T)
  rule true  && E => E
  rule false && _ => false
  rule true  || _ => true
  rule false || E => E


//  rule V:Val[N1:Int, N2:Int, Vs:Vals] => V[N1][N2, Vs]
//    [structural, anywhere]
  rule V:Val[N1:Int, N2:Int, Vs:Vals] => V[N1][N2, Vs]  [structural]
  rule lvalue(V:Val[N1:Int, N2:Int, Vs:Vals] => V[N1][N2, Vs])  [structural]

//  rule array(L,_)[N:Int] => lookup(L +Int N)
//    [structural, anywhere]
  rule array(L,_)[N:Int] => lookup(L +Int N)  [structural]
  rule lvalue(array(L,_)[N:Int] => lookup(L +Int N))  [structural]


  rule sizeOf(array(_,N)) => N


/*@ The semantics of function application needs to change into dynamic
method dispatch invocation, which is defined shortly.  However,
interestingly, the semantics of return stays unchanged. */

  rule <k> return(V:Val); ~> _ => V ~> K </k>
       <control>
         <fstack> ListItem((Env,K,C)) => .List ...</fstack>
         (_ => C)
       </control>
       <env> _ => Env </env>

  syntax Val ::= "nothing"
  rule return; => return nothing;   [macro]


  rule <k> read() => I ...</k> <in> ListItem(I:Int) => .List ...</in>  [read]


  context (HOLE => lvalue(HOLE)) = _

  rule <k> loc(L) = V:Val => V ...</k> <store>... L |-> (_ => V) ...</store>
    [assignment]


  rule {} => .  [structural]
  rule <k> { S } => S ~> env(Env) ...</k>  <env> Env </env>  [structural]


  rule S1::Stmts S2::Stmts => S1 ~> S2  [structural]

  rule _:Val; => .

  rule if ( true) S else _ => S
  rule if (false) _ else S => S

  rule while (E) S => if (E) {S while(E)S}  [structural]

  rule <k> print(V:Val, Es => Es); ...</k> <out>... .List => ListItem(V) </out>
    [print]
  rule print(.Vals); => .  [structural]


  syntax KItem ::= (Id,Stmt,K,Map,ControlCellFragment)

  syntax KItem ::= "popx"

  rule <k> (try S1 catch(X) {S2} => S1 ~> popx) ~> K </k>
       <control>
         <xstack> .List => ListItem((X, S2, K, Env, C)) ...</xstack>
         C
       </control>
       <env> Env </env>

  rule <k> popx => . ...</k>
       <xstack> ListItem(_) => .List ...</xstack>

  rule <k> throw V:Val; ~> _ => { var X = V; S2 } ~> K </k>
       <control>
         <xstack> ListItem((X, S2, K, Env, C)) => .List ...</xstack>
         (_ => C)
       </control>
       <env> _ => Env </env>

/*@ Thread spawning needs a new semantics, because we want the child
thread to also share the object environment with its parent.  The new
semantics of thread spawning will be defined shortly.  However,
interestingly, the other concurrency constructs keep their semantics
from SIMPLE unchanged. */

  rule (<thread>... <k>.</k> <holds>H</holds> <id>T</id> ...</thread> => .)
       <busy> Busy => Busy -Set keys(H) </busy>
       <terminated>... .Set => SetItem(T) ...</terminated>

  rule <k> join T:Int; => . ...</k>
       <terminated>... SetItem(T) ...</terminated>

  rule <k> acquire V:Val; => . ...</k>
       <holds>... .Map => V |-> 0 ...</holds>
       <busy> Busy (.Set => SetItem(V)) </busy>
    when (notBool(V in Busy:Set))  [acquire]

  rule <k> acquire V; => . ...</k>
       <holds>... V:Val |-> (N:Int => N +Int 1) ...</holds>

  rule <k> release V:Val; => . ...</k>
       <holds>... V |-> (N => N:Int -Int 1) ...</holds>
    when N >Int 0

  rule <k> release V; => . ...</k> <holds>... V:Val |-> 0 => .Map ...</holds>
       <busy>... SetItem(V) => .Set ...</busy>

  rule <k> rendezvous V:Val; => . ...</k>
       <k> rendezvous V; => . ...</k>  [rendezvous]

//@ \subsection{Unchanged auxiliary operations from untyped SIMPLE}

  syntax Decl ::= mkDecls(Ids,Vals)  [function]
  rule mkDecls((X:Id, Xs:Ids), (V:Val, Vs:Vals)) => var X=V; mkDecls(Xs,Vs)
  rule mkDecls(.Ids,.Vals) => {}

  syntax KItem ::= lookup(Int)
  rule <k> lookup(L) => V ...</k> <store>... L |-> V:Val ...</store>  [lookup]

  syntax KItem ::= env(Map)
  rule <k> env(Env) => . ...</k>  <env> _ => Env </env>  [structural]
  rule (env(_) => .) ~> env(_)  [structural]

  syntax Exp ::= lvalue(K)
  syntax Val ::= loc(Int)

  rule <k> lvalue(X:Id => loc(L)) ...</k> <env>... X |-> L:Int ...</env>
    [structural]

  context lvalue(_::Exp[HOLE::Exps])
  context lvalue(HOLE::Exp[_::Exps])

  rule lvalue(lookup(L:Int) => loc(L))  [structural]


  syntax Map ::= Int "..." Int "|->" K
    [function, latex({#1}\ldots{#2}\mapsto{#3})]
  rule N...M |-> _ => .Map  when N >Int M
  rule N...M |-> K => N |-> K (N +Int 1)...M |-> K  when N <=Int M


/*@ \subsection{Changes to the existing untyped SIMPLE semantics}

When we extend a language, sometimes we need to do more than just add
new language constructs and semantics for them.  Sometimes we want to
also extend the semantics of existing language constructs, in order to
get more from them. */

/*@ \subsubsection{Program initialization}

In SIMPLE, once all the global declarations were processed, the
function \texttt{main()} was invoked.  In KOOL, the global
declarations are classes, and their specific semantics is given
shortly; essentially, they are pre-processed one by one and added
into the \textsf{class} cell structure in the configuration.
Once all the classes are processed, the computation item
\texttt{execute}, which was placed right after the program in the
initial configuration, is reached.  In SIMPLE, the program was
initialized by calling the method \texttt{main()}.  In KOOL, the
program is initialized by creating an object instance of class
\texttt{Main}.  This will also implicitly call the method
\texttt{Main()} (the \texttt{Main} class constructor).  The emptiness
of the \textsf{env} cell below is just a sanity check, to make sure
that the user has not declared anything but classes at the top level
of the program. */

  syntax KItem ::= "execute"
  rule <k> execute => new Main(.Exps); </k> <env> .Map </env>  [structural]

/*@ The semantics of \texttt{new} (defined below) requires the
execution of all the class' declarations (and also of its
superclasses'). */


/*@ \subsubsection{Object and method closures}

Before we can define the semantics of method application (previously
called function application in SIMPLE), we need to add two more values
to the language, namely object and method closures: */

  syntax Val ::= objectClosure(CrntObjCellFragment)
               | methodClosure(Id,Int,Ids,Stmt)

/*@  An object value consists of an \texttt{objectClosure}-wrapped bag
containing the current class of the object and the environment stack
of the object.  The current class of an object will always be one of
the classes mapped to an environment in the environment stack of the
object.  A method closure encapsulates the method's parameters and
code (last two arguments), as well as the object context in which the
method code should execute.  This object context includes the current
class of the object (the first argument of \texttt{methodClosure}) and
the object environment stack (located in the object stored at the
location specified as the second argument of \texttt{methodClosure}). */


/*@ \subsubsection{Method application}

KOOL has a complex mechanism to invoke methods, because it allows both
dynamic method dispatch and methods as first-class-citizen values (the
latter making it a higher-order language).  The invocation mechanism
will be defined later.  What is sufficient to know for now is that
the two arguments of the application construct eventually reduce to
values, the first being a method closure and the latter a list of
values.  The semantics of the method closure application is then as
expected: the local environment and control are stacked, then we
switch to method closure's class and object environment and execute
the method body.  The \texttt{mkDecls} construct is the one that came
with the unchanged semantics of SIMPLE above.  */

  syntax KItem ::= (Map,K,ControlCellFragment)

  rule <k> methodClosure(Class,OL,Xs,S)(Vs:Vals) ~> K
           => mkDecls(Xs,Vs) S return; </k>
       <env> Env => .Map </env>
       <store>... OL |-> objectClosure(<crntClass>_</crntClass> Obj)...</store>
       <br/>
       <control>
          C
          <fstack> .List => ListItem((Env, K, C <crntObj> Obj' </crntObj>))
          ...</fstack>
          <crntObj> Obj' => <crntClass> Class </crntClass> Obj </crntObj>
       </control>


/*@ \subsubsection{Spawn}

We want to extend the semantics of \texttt{spawn} to also share the
current object environment with the child thread, in addition to the
current environment.  This extension will allow us to also use method
invocations in the spawned statements, which will be thus looked up as
expected, using dynamic method dispatch.  This lookup operation would
fail if the child thread did not have access to its parent's object
environment. */

  rule <thread>...
         <k> spawn S => !T:Int ...</k>
         <env> Env </env>
         <crntObj> Obj </crntObj>
       ...</thread>
       (. => <thread>...
               <k> S </k>
               <env> Env </env>
               <id> !T </id>
               <crntObj> Obj </crntObj>
             ...</thread>)


//@ \subsection{Semantics of the new KOOL constructs}

/*@ \subsubsection{Class declaration}

Initially, the classes forming the program are moved into their
corresponding cells: */

  rule <k> class Class1 extends Class2 { S } => . ...</k>
       <classes>... (. => <class>
                            <className> Class1 </className>
                            <extends> Class2 </extends>
                            <declarations> S </declarations>
                        </class>)
       ...</classes>  [structural]

/*@ \subsubsection{Method declaration}

Like in SIMPLE, method names are added to the environment and bound
to their code.  However, unlike in SIMPLE where each function was
executed in the same environment, namely the program global
environment, a method in KOOL needs to be executed into its object's
environment.  Thus, methods evaluate to closures, which encapsulate
their object's context (i.e., the current class and environment stack
of the object) in addition to method's parameters and body.  This
approach to bind method names to method closures in the environment
will also allow objects to pass their methods to other objects, to
dynamically change their methods by assigning them other method
closures, and even to allow all these to be done from other objects.
This gives the KOOL programmer a lot of power; one should use this
power wisely, though, because programs can become easily hard to
understand and reason about if one overuses these features. */

  rule <k> method F:Id(Xs:Ids) S => . ...</k>
       <crntClass> Class:Id </crntClass>
       <location> OL:Int </location>
       <env> Env => Env[F <- L] </env>
       <store>... .Map => L |-> methodClosure(Class,OL,Xs,S) ...</store>
       <nextLoc> L => L +Int 1 </nextLoc>


/*@ \subsubsection{New}

The semantics of \texttt{new} consists of two actions: memory
allocation for the new object and execution of the corresponding
constructor.  Then the created object is returned as the result of the
\texttt{new} operation; the value returned by the constructor, if any,
is discarded.  The current environment and object are stored onto the
stack and recovered after new (according to the semantics of
\texttt{return} borrowed from SIMPLE, when the statement
``\texttt{return this;}'' in the rule below is reached and evaluated),
because the object creation part of \texttt{new} will destroy them.
The rule below also initializes the object creation process by
emptying the local environment and the current object, and allocating
a location in the store where the created object will be eventually
stored (this is what the ``\texttt{storeObj}'' task after the object
creation task in the rule below will do---its rule is defined
shortly).  The location where the object will be stored is also made
available in the \textsf{crntObj} cell, so that method closures can
refer to it (see rule above). */

  syntax KItem ::= (Id,BagItem) // TODO: used to be ListItem; explain this

  rule <k> new Class:Id(Vs:Vals) ~> K
           => create(Class) ~> storeObj ~> Class(Vs); return this; </k>
       <env> Env => .Map </env>
       <nextLoc> L:Int => L +Int 1 </nextLoc>
       <br/>
       <control> C
         <crntObj> Obj
                   => <crntClass> Object </crntClass>
                      <envStack> ListItem((Object, <env>.Map</env>)) </envStack>
                      <location> L </location>
         </crntObj>
         <fstack> .List => ListItem((Env, K, C <crntObj> Obj </crntObj>)) ...</fstack>
       </control>

/*@ The creation of a new object (the memory allocation part only) is
a recursive process, requiring to first create an object for the
superclass.  A memory object representation is a layered structure:
for each class on the path from the instance class to the root of the
hierarchy there is a layer including the memory allocated for the
members (both fields and methods) of that class. */

  syntax KItem ::= create(Id)

  rule <k> create(Class:Id)
           => create(Class1) ~> setCrntClass(Class) ~> S ~> addEnvLayer ...</k>
       <className> Class </className>
       <extends> Class1:Id </extends>
       <declarations> S </declarations>  [structural]

  rule <k> create(Object) => . ...</k>  [structural]

/*@ The next operation sets the current class of the current object.
This is necessary to be done at each layer, because the current class
of the object is enclosed as part of the method closures (see the
semantics of method declarations above). */

  syntax KItem ::= setCrntClass(Id)

  rule <k> setCrntClass(C) => . ...</k>
       <crntClass> _ => C </crntClass>  [structural]

/*@ The next operation adds a new tagged environment layer to the
current object and gets ready for the next layer by clearing the
environment (note that \texttt{create} expects the environment to be
empty). */

  syntax KItem ::= "addEnvLayer"

  rule <k> addEnvLayer => . ...</k>
       <env> Env => .Map </env>
       <crntClass> Class:Id </crntClass>
       <envStack> .List => ListItem((Class, <env>Env</env>)) ...</envStack>
    [structural]

/*@ The following operation stores the created object at the location
reserved by \texttt{new}.  Note that the location reserved by
\texttt{new} was temporarily stored in the \textsf{crntObj} cell
precisely for this purpose.  Now that the newly created object is
stored at its location and that all method closures are aware of it,
the location is unnecessary and thus we delete it from the
\textsf{crntObj} cell. */

  syntax KItem ::= "storeObj"

  rule <k> storeObj => . ...</k>
       <crntObj> Obj (<location> L:Int </location> => .) </crntObj>
       <store>... .Map => L |-> objectClosure(Obj) ...</store>


/*@ \subsubsection{Self reference}

The semantics of \texttt{this} is straightforward: evaluate to the
current object. */

  rule <k> this => objectClosure(Obj) ...</k>
       <crntObj> Obj </crntObj>


/*@ \subsubsection{Object member access}

We can access an object member (field or method) either explicitly,
using the construct \texttt{e.x}, or implicitly, using only the member
name \texttt{x} directly.  The borrowed semantics of SIMPLE will
already lookup a sole name in the local environment.  The first rule
below reduces implicit member access to explicit access when the name
cannot be found in the local environment.  There are two cases to
analyze for explicit object member access, depending upon whether the
object is a proper object or it is just a redirection to the parent
class via the construct \texttt{super}.  In the first case, we
evaluate the object expression and lookup the member starting with the
current class (static scoping).  Note the use of the conditional
evaluation context.  In the second case, we just lookup the member
starting with the superclass of the current class.  In both cases,
the \texttt{lookupMember} task eventually yields a \texttt{lookup(L)}
task for some appropriate location \texttt{L}, which will be further
solved with the corresponding rule borrowed from SIMPLE.  Note that the
current object is not altered by \texttt{super}, so future method
invocations see the entire object, as needed for dynamic method dispatch. */

  rule <k> X:Id => this . X ...</k> <env> Env:Map </env>
    when notBool(X in keys(Env))  [structural]

  context HOLE._::Id when (HOLE =/=K super)

// TODO: explain how Assoc matching has been replaced with two rules here.
// Maybe also improve it a bit.

/*  rule objectClosure(<crntClass> Class:Id </crntClass>
                     <envStack>... (Class,EnvC) EStack </envStack>)
       . X:Id
    => lookupMember(<envStack> (Class,EnvC) EStack </envStack>, X)
    [structural]*/

  rule objectClosure(<crntClass> Class:Id </crntClass>
                     <envStack> ListItem((Class,EnvC:BagItem)) EStack </envStack>)
       . X:Id
    => lookupMember(<envStack> ListItem((Class,EnvC)) EStack </envStack>, X)
    [structural]
  rule objectClosure(<crntClass> Class:Id </crntClass>
                     <envStack> ListItem((Class':Id,_)) => .List ...</envStack>)
       . X:Id
    when Class =/=K Class'  [structural]

/*  rule <k> super . X => lookupMember(<envStack>EStack</envStack>, X) ...</k>
       <crntClass> Class </crntClass>
       <envStack>... (Class,EnvC) EStack </envStack>
    [structural]*/
  rule <k> super . X => lookupMember(<envStack>EStack</envStack>, X) ...</k>
       <crntClass> Class:Id </crntClass>
       <envStack> ListItem((Class,_)) EStack </envStack>
    [structural]
  rule <k> super . X ...</k>
       <crntClass> Class </crntClass>
       <envStack> ListItem((Class':Id,_)) => .List ...</envStack>
    when Class =/=K Class'  [structural]

/*@\subsubsection{Method invocation}

Unlike in SIMPLE, in KOOL application was declared strict only in its
second argument.  That is because we want to ensure dynamic method
dispatch when the first argument is a method access.  As a
consequence, we need to consider all the cases of interest for the
first argument and to explicitly say what to do in each case.  In all
cases except for method access in a proper object (i.e., not
\texttt{super}), we want the same behavior for the first argument as
if it was not in a method invocation position.  When it is a member
access (the third rule below), we look it up starting with the
instance class of the corresponding object.  This ensures dynamic
dispatch for methods; it actually dynamically dispatches field
accesses, too, which is correct in KOOL, because one can assign method
closures to fields and the field appeared in a method invocation
context.  The last context declaration below says that method
applications or array accesses are also allowed as first argument to
applications; that is because methods are allowed to return methods
and arrays are allowed to hold methods in KOOL, since it is
higher-order.  If that is the case, then we want to evaluate the
method call or the array access.  */

  rule <k> (X:Id => V)(_:Exps) ...</k>
       <env>... X |-> L ...</env>
       <store>... L |-> V:Val ...</store>  [lookup]

  rule <k> (X:Id => this . X)(_:Exps) ...</k>
       <env> Env </env>
    when notBool(X in keys(Env))  [structural]

  context HOLE._::Id(_) when HOLE =/=K super

  rule (objectClosure(Obj:Bag <envStack> EStack </envStack>) . X
    => lookupMember(<envStack> EStack </envStack>, X:Id))(_:Exps)  [structural]

/*  rule <k> (super . X
            => lookupMember(<envStack>EStack</envStack>,X))(_:Exps)...</k>
       <crntClass> Class </crntClass>
       <envStack>... (Class,_) EStack </envStack>
    [structural]*/
  rule <k> (super . X
            => lookupMember(<envStack>EStack</envStack>,X))(_:Exps)...</k>
       <crntClass> Class </crntClass>
       <envStack> ListItem((Class,_)) EStack </envStack>
    [structural]
  rule <k> (super . X)(_:Exps) ...</k>
       <crntClass> Class </crntClass>
       <envStack> ListItem((Class':Id,_)) => .List ...</envStack>
    when Class =/=K Class'  [structural]

  context HOLE(_:Exps)
    when getKLabel HOLE ==KLabel '_`(_`) orBool getKLabel HOLE ==KLabel '_`[_`]

/*@ Eventually, each of the rules above produces a \texttt{lookup(L)}
task as a replacement for the method.  When that happens, we just
lookup the value at location \texttt{L}: */

  rule <k> (lookup(L) => V)(_:Exps) ...</k>  <store>... L |-> V:Val ...</store>
    [lookup]

/*@  The value $V$ looked up above is expected to be a method closure,
in which case the semantics of method application given above will
apply.  Otherwise, the execution will get stuck. */


/*@ \subsubsection{Instance Of}

It searches the object environment for a layer corresponding to the
desired class.  It returns \texttt{true} iff it can find the class,
otherwise it returns \texttt{false}; it only gets stuck when its first
argument does not evaluate to an object.  */

  rule objectClosure(<envStack> ListItem((C,_)) ...</envStack> _)
       instanceOf C => true

  rule objectClosure(<envStack> ListItem((C::Id,_)) => .List ...</envStack> _)
       instanceOf C'  when C =/=K C'  [structural]
//TODO: remove the sort cast ::Id of C above, when sort inference bug fixed

  rule objectClosure(<envStack> .List </envStack> _) instanceOf _ => false


/*@ \subsubsection{Cast}

In untyped KOOL, we prefer to not check the validity of casting.  In
other words, any cast is allowed on any object, simply changing the
current class of the object to the desired class.  The execution will
get stuck later if one attempts to access a field which is not
available.  Moreover, the execution may complete successfully even
in the presence of invalid casts, provided that each accessed member
during the current execution is, or happens to be, available.  */

  rule (C) objectClosure(<crntClass> _ </crntClass> Obj)
    => objectClosure(<crntClass> C </crntClass> Obj)


/*@ \subsection{KOOL-specific auxiliary declarations and operations}

Here we define all the auxiliary constructs used in the above
KOOL-specific semantics (those used in the SIMPLE fragment
have already been defined in a corresponding section above). */

/*@ \subsubsection{Objects as lvalues}

The current machinery borrowed with the semantics of SIMPLE allows us
to enrich the set of lvalues, this way allowing new means to assign
values to locations.  In KOOL, we want object member names to be
lvalues, so that we can assign values to them using the already
existing machinery.  The first rule below ensures that the object is
always explicit, the evaluation context enforces the object to be
evaluated, and finally the second rule initiates the lookup for the
member's location based on the current class of the object. */

  rule <k> lvalue(X:Id => this . X) ...</k>  <env> Env </env>
    when notBool(X in keys(Env))  [structural]

  context lvalue(HOLE . _)

/*  rule lvalue(objectClosure(<crntClass> C </crntClass>
                            <envStack>... (C,EnvC) EStack </envStack>)
              . X
              => lookupMember(<envStack> (C,EnvC) EStack </envStack>,
                              X))  [structural]*/
  rule lvalue(objectClosure(<crntClass> Class </crntClass>
                            <envStack> ListItem((Class,EnvC:BagItem)) EStack </envStack>)
              . X
              => lookupMember(<envStack> ListItem((Class,EnvC)) EStack </envStack>,
                              X))  [structural]
  rule lvalue(objectClosure(<crntClass> Class </crntClass>
                            <envStack> ListItem((Class':Id,_)) => .List ...</envStack>)
              . X)
    when Class =/=K Class'  [structural]


/*@ \subsubsection{Lookup member}

It searches for the given member in the given environment stack,
starting with the most concrete class and going up in the hierarchy. */

  syntax KItem ::= lookupMember(BagItem,Id)  [function]

//  rule lookupMember(<envStack> (_, <env>... X|->L ...</env>) ...</envStack>, X)
//    => lookup(L)
  rule lookupMember(<envStack> ListItem((_, <env>... X|->L ...</env>)) ...</envStack>, X)
    => lookup(L)

//  rule lookupMember(<envStack> (_, <env> Env </env>) => .List ...</envStack>, X)
//    when notBool(X in keys(Env))
  rule lookupMember(<envStack> ListItem((_, <env> Env </env>)) Rest </envStack>, X) =>
       lookupMember(<envStack> Rest </envStack>, X)
    when notBool(X in keys(Env))
//TODO: beautify the above

endmodule
