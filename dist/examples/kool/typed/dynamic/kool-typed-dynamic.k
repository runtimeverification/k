/*!
\title{KOOL --- Typed --- Dynamic}
\author{Grigore Ro\c{s}u and Traian Florin \c{S}erb\u{a}nu\c{t}\u{a}
        (\texttt{\{grosu,tserban2\}@illinois.edu})}
\organization{University of Illinois at Urbana-Champaign}
*/

/*@
\section{Abstract}
This is the \K dynamic semantics of the typed KOOL language.  It is
very similar to the semantics of the untyped KOOL, the difference
being that we now check the typing policy dynamically.  Since we have
to now declare the types of variables and methods, we adopt a syntax
for those which is closed to that of Java.  Like in the semantics of
untyped KOOL, where we borrowed almost all the semantics of untyped
SIMPLE, we are going to also borrow much of the semantics of
dynamically typed SIMPLE here.  We will highlight the differences
between the dynamically typed and the untyped KOOL as we proceed with
the semantics. */

module KOOL-TYPED-DYNAMIC-SYNTAX

/*@ \section{Syntax}
Like for the untyped KOOL language, the syntax of typed KOOL extends
that of typed SIMPLE with object-oriented constructs.
 */

/*@ \subsection{Syntax from SIMPLE}
The syntax below is taken ad litteram from dynamically typed SIMPLE.
Like in untyped KOOL, we removed from the \K annotated syntax of
SIMPLE the construct for function declarations (because we want to
call them methods now) and the one for function application (because
application is not strict in the first argument anymore due to dynamic
method dispatch).  Moreover, we removed the syntax of \texttt{try-catch}
from that of SIMPLE, because we want to have typed exceptions in KOOL. */

/*@ \subsection{KOOL Additional Syntax}
The KOOL syntactic extensions below are almost identical to their
untyped variants in untyped KOOL.  The only difference is that we add
a new type construct for class types and that now methods take typed
arguments (we achieved this the same way as in typed SIMPLE) and can
also have an explicit return type.  As a convenience to the
programmer, a macro adds an explicit type \texttt{void} whenever a
return type is not provided (e.g., one may not want to write a return
type for constructors in KOOL typed programs).  The syntax of typed
exceptions differs from that of typed SIMPLE in that the variable
bound by \texttt{catch} is now expected to be typed (we use
\textit{Exp}, but we only give semantics for the case when it has the
form \textit{Id:Type}. */

  syntax Id ::= "Object" | "Main"

//@ \subsection{Types}

  syntax Type ::= "void" | "int" | "bool" | "string"
                | Id                              // KOOL class
                | Type "[" "]"
                > Types "->" Type
                | "(" Type ")"           [bracket]
  syntax Types ::= List{Type,","}

//@ \subsection{Declarations}

  syntax Param ::= Type Id
  syntax Params ::= List{Param,","}

  syntax Decl ::= Type Exps ";"
                | Type Id "(" Params ")" Block    // stays like in typed SIMPLE
                | "class" Id Block                // KOOL
                | "class" Id "extends" Id Block   // KOOL    

//@ \subsection{Expressions}

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

  syntax Exps ::= List{Exp,","}          [strict]

//@ \subsection{Statements}

  syntax Block ::= "{" "}"
                | "{" Stmts "}"

  syntax Stmt ::= Decl | Block
                | Exp ";"                               [strict]
                | "if" "(" Exp ")" Block "else" Block   [avoid, strict(1)]
                | "if" "(" Exp ")" Block
                | "while" "(" Exp ")" Block
                | "for" "(" Stmt Exp ";" Exp ")" Block
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

//@ \subsection{Desugaring macros}
  rule if (E) S => if (E) S else {}                                     [macro]
  rule for(Start Cond; Step) {S:Stmts} => {Start while(Cond){S Step;}}  [macro]
  rule T:Type E1:Exp, E2:Exp, Es:Exps; => T E1; T E2, Es;               [macro]
  rule T:Type X:Id = E; => T X; X = E;                                  [macro]

  rule class C:Id S => class C extends Object S                     // KOOL

endmodule


/*@ \section{Semantics}
We first discuss the new configuration, then we include the semantics of
the constructs borrowed from SIMPLE which stay unchanged, and then we
discuss the semantics of the additional KOOL constructs and of those
from SIMPLE whose smeantics had to change. */

module KOOL-TYPED-DYNAMIC
  imports KOOL-TYPED-DYNAMIC-SYNTAX

/*@ \subsection{Configuration}
The configuration of dynamically typed KOOL is almost identical to
that of its untyped variant.  The only difference is the cell
\textsf{return}, inside the \textsf{control} cell, whose role is to
hold the expected return type of the invoked method.  That is because
we want to dynamically check that the value that a method returns has
the expected type. */

  configuration <T color="red">
                  <threads color="orange">
                    <thread multiplicity="*" color="yellow">
                      <k color="green"> ($PGM:Stmts ~> execute) </k>
                      <br/>
                      <control color="cyan">
                        <fstack color="blue"> .List </fstack>
                        <xstack color="purple"> .List </xstack>
                        <return color="LimeGreen"> void </return>  // KOOL
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

/*@ \subsection{Unchanged semantics from dynamically typed SIMPLE}
The semantics below is taken over from dynamically typed SIMPLE
unchanged.  Like for untyped KOOL, the semantics of function/method
declaration and invocation, and of program initialization needs to
change.  Moreover, due to subtyping, the semantics of several imported
SIMPLE constructs can be made more general, such as that of the
return statement and of the the assignment.  Finally, since the
exceptions are now typed, they also need a different semantics.  We
removed all these from the imported semantics of SIMPLE below and gave
their typed KOOL semantics right after, together with the extended
semantics of thread spawning (which is identical to that of untyped
KOOL).  */

  syntax Val ::= Int | Bool | String
               | array(Type,Int,Int)
  syntax Vals ::= List{Val,","}
  syntax Exp ::= Val
  syntax KResult ::= Val


  syntax K ::= undefined(Type)  [latex(\bot_{#1})]

  rule <k> T:Type X:Id; => . ...</k>
       <env> Env => Env[L/X] </env>
       <store>... . => L |-> undefined(T) ...</store>
       <nextLoc> L:Int => L +Int 1 </nextLoc>


  rule <k> T:Type X:Id[N:Int]; => . ...</k>
       <env> Env => Env[L/X] </env>
       <store>... . => L |-> array(T, L +Int 1, N)
                       (L +Int 1)...(L +Int N) |-> undefined(T) ...</store>
       <nextLoc> L:Int => L +Int 1 +Int N </nextLoc>
    when N >=Int 0

  context _:Type _[HOLE];


  syntax Id ::= "$1" | "$2"
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


  rule <k> X:Id => V ...</k>
       <env>... X |-> L ...</env>
       <store>... L |-> V:Val ...</store>  [lookup]


  context ++(HOLE => lvalue(HOLE))
  rule <k> ++loc(L) => I +Int 1 ...</k>
       <store>... L |-> (I:Int => I +Int 1) ...</store>  [increment]


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


  rule V:Val[N1:Int, N2:Int, Vs:Vals] => V[N1][N2, Vs]
    [structural, anywhere]

  rule array(_:Type, L:Int, M:Int)[N:Int] => lookup(L +Int N)
    when N >=Int 0 andBool N <Int M  [structural, anywhere]

  rule sizeOf(array(_,_,N)) => N


  syntax Val ::= nothing(Type)
  rule <k> return; => return nothing(T); ...</k> <return> T </return>
    [structural]


  rule <k> read() => I ...</k> <in> ListItem(I:Int) => . ...</in>  [read]


  context (HOLE => lvalue(HOLE)) = _


  rule {} => .  [structural]
  rule <k> { S } => S ~> env(Env) ...</k>  <env> Env </env>  [structural]


  rule S1:Stmts S2:Stmts => S1 ~> S2  [structural]


  rule _:Val; => .


  rule if ( true) S else _ => S
  rule if (false) _ else S => S


  rule while (E) S => if (E) {S while(E)S}  [structural]


  rule <k> print(V:Val, Es => Es); ...</k> <out>... . => ListItem(V) </out>
    when typeOf(V) ==K int orBool typeOf(V) ==K string  [print]
  rule print(.Vals); => .  [structural]


   rule (<thread>... <k>.</k> <holds>H</holds> <id>T</id> ...</thread> => .)
        <busy> Busy => Busy -Set keys(H) </busy>
        <terminated>... . => SetItem(T) ...</terminated>

   rule <k> join T:Int; => . ...</k>
        <terminated>... SetItem(T) ...</terminated>

   rule <k> acquire V:Val; => . ...</k>
        <holds>... . => V |-> 0 ...</holds>
        <busy> Busy (. => SetItem(V)) </busy>
     when (notBool(V in Busy:Set))  [acquire]

   rule <k> acquire V; => . ...</k>
        <holds>... V:Val |-> (N:Int => N +Int 1) ...</holds>

   rule <k> release V:Val; => . ...</k>
        <holds>... V |-> (N => N:Int -Int 1) ...</holds>
      when N >Int 0

   rule <k> release V; => . ...</k> <holds>... V:Val |-> 0 => . ...</holds>
        <busy>... SetItem(V) => . ...</busy>

   rule <k> rendezvous V:Val; => . ...</k>
        <k> rendezvous V; => . ...</k>  [rendezvous]

//@ \subsubsection{Auxiliary operations}

  syntax Decl ::= mkDecls(Params,Vals)  [function]
  rule mkDecls((T:Type X:Id, Ps:Params), (V:Val, Vs:Vals))
    => T X=V; mkDecls(Ps,Vs)
  rule mkDecls(.Params,.Vals) => {}

  syntax K ::= lookup(Int)
  rule <k> lookup(L) => V ...</k> <store>... L |-> V:Val ...</store>  [lookup]

  syntax K ::= env(Map)
  rule <k> env(Env) => . ...</k>  <env> _ => Env </env>  [structural]
  rule (env(_) => .) ~> env(_)  [structural]

  syntax Exp ::= lvalue(K)
  syntax Val ::= loc(Int)
  rule <k> lvalue(X:Id) => loc(L) ...</k>  <env>... X |-> L:Int ...</env>
    [structural]

  context lvalue(_[HOLE])
  context lvalue(HOLE[_])

  rule lvalue(lookup(L:Int)) => loc(L)  [structural]

  syntax Type ::= Type "<" Vals ">"  [function]
  rule T:Type<_,Vs:Vals> => T[]<Vs>
  rule T:Type<.Vals> => T

  syntax Map ::= Int "..." Int "|->" K
    [function, latex({#1}\ldots{#2}\mapsto{#3})]
  rule N...M |-> _ => .Map  when N >Int M
  rule N...M |-> K => N |-> K (N +Int 1)...M |-> K  when N <=Int M

  syntax Type ::= typeOf(K)  [function]
  rule typeOf(_:Int) => int
  rule typeOf(_:Bool) => bool
  rule typeOf(_:String) => string
  rule typeOf(array(T,_,_)) => (T[])   // () needed! K parses [] as "no tags"   
  rule typeOf(undefined(T)) => T
  rule typeOf(nothing(T)) => T

  syntax Types ::= getTypes(Params)  [function]
  rule getTypes(T:Type _:Id) => T, .Types   // I would like to not use .Types   
  rule getTypes(T:Type _:Id, P, Ps) => T, getTypes(P,Ps)
  rule getTypes(.Params) => void, .Types


/*@ \subsection{Changes to the existing dynamically typed SIMPLE Semantics}
We extend/change the semantics of several SIMPLE constructs in order
to take advantage of the richer KOOL semantic infrastructure and thus
get more from the existing SIMPLE constructs. */

/*@ \subsubsection{Spawn}
Like in untyped KOOL. */

  rule <thread>...
         <k> spawn S => T ...</k>
         <env> Env </env>
         <crntObj> Obj </crntObj>
       ...</thread>
       (. => <thread>...
               <k> S </k>
               <env> Env </env>
               <id> T </id>
               <crntObj> Obj </crntObj>
             ...</thread>)
    when fresh(T:Int)


/*@ \subsection{Assignment}
Typed KOOL allows to assign subtype instance values to supertype lvalues. */

  rule <k> loc(L) = V:Val
           => subtype(typeOf(V),typeOf(V')) ~> true?
              ~> unsafeCast(V, typeOf(V')) ...</k>
       <store>... L |-> (V' => unsafeCast(V, typeOf(V'))) ...</store>
    [assignment]


/*@ \subsubsection{Typed exceptions}
Exceptions are propagated now until a catch that can handle them is
encountered. */

  syntax ListItem ::= (Param,Stmt,K,Map,Bag)
  syntax K ::= "popx"

  rule <k> (try S1 catch(P) S2 => S1 ~> popx) ~> K </k>
       <control>
         <xstack> . => (P, S2, K, Env, C) ...</xstack>
         C
       </control>
       <env> Env </env>

  rule <k> popx => . ...</k>
       <xstack> _:ListItem => . ...</xstack>

  rule <k> throw V:Val; ~> _
        => if (subtype(typeOf(V),T)) { T X = V; S2 } else { throw V; } ~> K
       </k>
       <control>
         <xstack> (T:Type X:Id, S2, K, Env, C) => . ...</xstack>
         (_ => C)
       </control>
       <env> _ => Env </env>


/*@ \subsection{Object and method closures}
The only change to untyped KOOL's values is that closures are now typed
(their last argument holds their type). */

 syntax Val ::= objectClosure(Bag)
              | methodClosure(Type,Id,Int,Params,Stmt)

/*@ \subsection{Class declaration}
Like in untyped KOOL. */

  rule <k> class Class1 extends Class2 { S } => . ...</k>
       <classes>... (. => <class>
                            <className> Class1 </className>
                            <extends> Class2 </extends>
                            <declarations> S </declarations>
                        </class>)
       ...</classes>  [structural]


/*@ \subsection{Program initialization}
Like in untyped KOOL. */

  syntax K ::= "execute"
  rule <k> execute => new Main(.Exps); </k> <env> . </env>  [structural]


/*@ \subsection{Method declaration}
Methods are now typed and we need to store their types in their
closures, so that their type contract can be checked at invocation
time.  The rule below is conceptually similar to that of untyped KOOL;
the only difference is the addition of the types. */

  rule <k> T:Type F:Id(Ps:Params) S => . ...</k>
       <crntClass> C </crntClass>
       <location> OL </location>
       <env> Env => Env[L/F] </env>
       <store>... . => L|->methodClosure(getTypes(Ps)->T,C,OL,Ps,S) ...</store>
       <nextLoc> L => L +Int 1 </nextLoc>


/*@ \subsection{New}
The semantics of \texttt{new} in dynamically typed KOOL is also
similar to that in untyped KOOL, the main difference being the
management of the return types.  Indeed, when a new object is created
we also have to stack the current type in the \textsf{return} cell in
order to be recovered after the creation of the new object.  Only the
first rule below needs to be changed; the others are identical to
those in untyped KOOL. */

  syntax ListItem ::= (Id,BagItem)
  // Id is the class name, BagItem is its corresponding environment

  rule <k> new Class:Id(Vs:Vals) ~> K
           => create(Class) ~> (storeObj ~> ((Class(Vs)); return this;)) </k>
       <env> Env => . </env>
       <nextLoc> L:Int => L +Int 1 </nextLoc>
       <br/>
       <control> C
         <crntObj> Obj
                   => <crntClass> Object </crntClass>
                      <envStack> (Object, <env>.Map</env>) </envStack>
                      <location> L </location>
         </crntObj>
         <return> T => Class </return>
         <fstack> . => (Env, K, C <return>T</return> <crntObj>Obj</crntObj>)
         ...</fstack>
       </control>

  syntax K ::= create(Id)

  rule <k> create(Class:Id)
           => create(Class1) ~> setCrntClass(Class) ~> S ~> addEnvLayer ...</k>
       <className> Class </className>
       <extends> Class1:Id </extends>
       <declarations> S </declarations>  [structural]

  rule <k> create(Object) => . ...</k>  [structural]

  syntax K ::= setCrntClass(Id)

  rule <k> setCrntClass(C) => . ...</k>
       <crntClass> _ => C </crntClass>  [structural]

  syntax K ::= "addEnvLayer"

  rule <k> addEnvLayer => . ...</k>
       <env> Env => . </env>
       <crntClass> Class:Id </crntClass>
       <envStack> . => (Class, <env>Env</env>) ...</envStack>
    [structural]

  syntax K ::= "storeObj"

  rule <k> storeObj => . ...</k>
       <crntObj> Obj (<location> L:Int </location> => .) </crntObj>
       <store>... . => L |-> objectClosure(Obj) ...</store>


/*@ \subsection{Self reference}
Like in untyped KOOL. */

  rule <k> this => objectClosure(Obj) ...</k>
       <crntObj> Obj </crntObj>


/*@ \subsection{Object member access}
Like in untyped KOOL. */

  rule <k> X:Id => this . X ...</k> <env> Env:Map </env>
    when notBool(X in keys(Env))  [structural]

  context HOLE . _ when (HOLE =/=K super)

  rule objectClosure(<crntClass> Class:Id </crntClass>
                     <envStack>... (Class,EnvC) EStack </envStack>)
       . X:Id
    => lookupMember(<envStack> (Class,EnvC) EStack </envStack>, X)
    [structural]

  rule <k> super . X => lookupMember(<envStack>EStack</envStack>, X) ...</k>
       <crntClass> Class </crntClass>
       <envStack>... (Class,EnvC) EStack </envStack>
    [structural]


/*@\subsection{Method invocation}
The method lookup is the same as in untyped KOOL.
The method closure application and return are slightly different,
since we need to check that the type of the returned value is an
instance of the claimed return type of the method.  The first group of
rules below are identical to those in untyped KOOL. */

  rule <k> (X:Id => V)(_:Exps) ...</k>
       <env>... X |-> L ...</env>
       <store>... L |-> V:Val ...</store>  [lookup]

  rule <k> (X:Id => this . X)(_:Exps) ...</k>
       <env> Env </env>
    when notBool(X in keys(Env))  [structural]

  context HOLE._(_) when HOLE =/=K super

  rule (objectClosure(Obj:Bag <envStack> EStack </envStack>) . X
    => lookupMember(<envStack> EStack </envStack>, X:Id))(_:Exps)  [structural]

  rule <k> (super . X
            => lookupMember(<envStack>EStack</envStack>,X))(_:Exps)...</k>
       <crntClass> Class </crntClass>
       <envStack>... (Class,_) EStack </envStack>
    [structural]

  context HOLE(_:Exps)
    when getKLabel HOLE ==KLabel '_`(_`) orBool getKLabel HOLE ==KLabel '_`[_`]

  rule <k> (lookup(L) => V)(_:Exps) ...</k>  <store>... L |-> V:Val ...</store>
    [lookup]

/*@ Closure application needs to also set a new return type in the
\textsf{return} cell, in order for the values returned by its body to
be checked against the return type of the method.  To do this correctly,
we also need to stack the current status of the \textsf{return} cell
and then pop it when the method returns. */

  syntax ListItem ::=  (Map,K,Bag)

// discuss the possible casting HERE!
// any why the type is stored differently here from in SIMPLE
  rule <k> methodClosure(_->T,Class,OL,Ps,S)(Vs:Vals) ~> K
           => mkDecls(Ps,Vs) S return; </k>
       <env> Env => . </env>
       <store>... OL |-> objectClosure(<crntClass>_</crntClass> Obj)...</store>
       <br/>
       <control>
          C
          <fstack> . => (Env, K, C <crntObj> Obj' </crntObj>
                                   <return> T' </return>) ...</fstack>
          <crntObj> Obj' => <crntClass> Class </crntClass> Obj </crntObj>
          <return> T' => T </return>
       </control>

/*@ At method return, we have to check that the type of the returned
value is a subtype of the expected return type.  Moreover, if that is
the case, then we also upcast the returned value to one of the
expected type. */

  rule <k> return V:Val; ~> _
           => subtype(typeOf(V), T) ~> true? ~> unsafeCast(V, T) ~> K
       </k>
       <control>
         <fstack> (Env, K, C) => . ...</fstack>
         (<return> T:Type </return> _ => C)
       </control>
       <env> _ => Env </env>


/*@ \subsection{Instance Of}
Like in untyped KOOL.  */

  rule objectClosure(<envStack> (C,_) ...</envStack> _)
       instanceOf C => true

  rule objectClosure(<envStack> (C,_) => . ...</envStack> _)
       instanceOf C'  when C =/=K C'  [structural]

  rule objectClosure(<envStack> . </envStack> _) instanceOf _ => false


/*@ \subsection{Cast}
Unlike in untyped KOOL, in typed KOOL we actually check that the object
can indeed be cast to the claimed type. */

  rule (C:Id) objectClosure(<crntClass> _ </crntClass> Obj)
    => objectClosure(Obj) instanceOf C ~> true?
       ~> objectClosure(<crntClass> C </crntClass> Obj)


/*@ \subsection{Objects as lvalues}
Like in untyped KOOL. */

  rule <k> lvalue(X:Id => this . X) ...</k>  <env> Env </env>
    when notBool(X in keys(Env))  [structural]

  context lvalue(HOLE . _)

  rule lvalue(objectClosure(<crntClass> C </crntClass>
                            <envStack>... (C,EnvC) EStack </envStack>)
              . X
              => lookupMember(<envStack> (C,EnvC) EStack </envStack>,
                              X))  [structural]


/*@ \subsection{Lookup member}
Like in untyped KOOL. */

  syntax K ::= lookupMember(BagItem,Id)  [function]

  rule lookupMember(<envStack> (_, <env>... X |-> L ...</env>)
                    ...</envStack>, X) => lookup(L)

  rule lookupMember(<envStack> (_, <env> Env </env>) => .
                    ...</envStack>, X)  when notBool(X in keys(Env))


//@ \subsection{Auxiliary operations}

/*@ \subsubsection{\texttt{typeOf}}
\texttt{typeOf} for the additional values. */

  rule typeOf(objectClosure(_ <crntClass> C </crntClass>)) => C
  rule typeOf(methodClosure(T:Type,_,_,Ps:Params,_)) => T


/*@ \subsubsection{Subtyping constraints}
The subclass relation introduces a subtyping relation. */

  syntax Exp ::= subtype(Types,Types)

  rule subtype(T:Type, T) => true  [structural]

  rule <k> subtype(C1:Id, C:Id) => subtype(C2, C) ...</k>
       <className> C1 </className>
       <extends> C2:Id </extends>
    when C1 =/=K C  [structural]

  rule subtype(Object,Class) => false
    when Class =/=K Object  [structural]

  rule subtype(Ts1->T2,Ts1'->T2') => subtype((T2,Ts1'),(T2',Ts1))

// note that the following rule would be wrong!
//  rule subtype(T[],T'[]) => subtype(T,T')

  rule subtype((T:Type,Ts),(T':Type,Ts')) => subtype(T,T') && subtype(Ts,Ts')
    when Ts =/=K .Types
  rule subtype(.Types,.Types) => true

/*@ \subsubsection{Unsafe Casting}
Performs unsafe casting.  One should only use it in combination with
the subtype relation above. */

  syntax Val ::= unsafeCast(Val,Type)  [function]

  rule unsafeCast(objectClosure(<crntClass>_</crntClass> Obj), C:Id)
    => objectClosure(<crntClass> C </crntClass> Obj)

  rule unsafeCast(methodClosure(T',C,OL,Ps,S), T) => methodClosure(T,C,OL,Ps,S)

  rule unsafeCast(V:Val, T:Type) => V  when typeOf(V) ==K T


/*@ \subsubsection{Generic guard}
A generic computational guard (should be builtin): it allows the
computation to continue only if a prefix guard evaluates to true. */

  syntax K ::= "true?"
  rule true ~> true? => .  [structural]

 endmodule
