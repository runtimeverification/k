
module KOOL-UNTYPED-SYNTAX

/*@ \section{Syntax}
The syntax of KOOL extends that of SIMPLE with object-oriented constructs.
We start by first including the syntax of SIMPLE that stays unchanged,
followed by the specific changes and additions of KOOL. */

/*@ \subsection{Syntax from SIMPLE}
The syntax below is taken ad litteram from SIMPLE.
We removed from the \K annotated syntax of SIMPLE two constructs, namely
the one for function declarations (because we want to call them methods now)
and the one for function application (because application is not strict in the
first argument anymore---needs to initiate dynamic method dispatch). */

  syntax #Id ::= "main"
  syntax Ids ::= List{#Id,","} [:prec(70):]

  syntax Decl ::= "var" Exps ";"

  syntax Exp ::= #Int | #Bool | #String | #Id
               | "++" Exp              [:prec(0):]
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
               | "read" "(" ")"
               | Exp "=" Exp           [:strict(2) prec(40) gather (e E):]
  syntax Exps ::= List{Exp,","}

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
                 | Stmts Stmts                      [:prec(100) gather(e E):]

  macro if E:Exp then S:Stmt = if E then S else {}
  macro (for X:#Id = E1 to E2 do S) = {var X=E1; while X <= E2 do {S X=X+1;}}
  macro var E1:Exp, E2:Exp, Es:Exps; = var E1; var E2, Es;
  macro var X = E; = var X; X = E;

/*@ \subsection{KOOL Additional Syntax}
We now introduce the new syntax of KOOL, which extends that of SIMPLE
above.  First, we need a new dedicated identifier, \texttt{object}, for the
default top-most class.  Second, we rename the \texttt{function} keyword of
SIMPLE into \texttt{method}.  Third, we add syntax for class declarations
together with a macro making classes which extend nothing to extend
\texttt{object}.  Fourth, we change the strictness attribute of application
into \texttt{strict(2)}.  Finally, we add syntax and corresponding strictness
for the KOOL object-oriented constructs. */

  syntax #Id ::= "object"

  syntax Decl ::= "method" #Id "(" Ids ")" Stmt

  syntax Decl ::= "class" #Id "{" Stmts "}"
                | "class" #Id "extends" #Id "{" Stmts "}"
  macro class Class:#Id {Ss:Stmts} = class Class extends object {Ss}

  syntax Exp ::=  Exp "(" Exps ")"       [:strict(2) prec(2):]

  syntax Exp ::= "new" #Id "(" Exps ")" [:strict(2) prec(1):]
               | "this"
               | "super"
               | Exp "." #Id            [:prec(1):]
               | Exp "instanceOf" #Id   [:prec(0) strict(1):]
               | "cast" Exp "to" #Id    [:prec(0) strict(1):]
end module


module KOOL-UNTYPED
  imports KOOL-UNTYPED-SYNTAX

/*@ \section{Semantics}
We first discuss the new configuration of KOOL, which extends that of
SIMPLE.  Then we include the semantics of the constructs borrowed from
SIMPLE unchanged; we refrain from discussing those, because they were
already discussed in the \K definition of SIMPLE.  Then we discuss
changes to SIMPLE's semantics, more precisely a slight extension to
the semantics of \texttt{spawn}.  Finally, we discuss in detail the
semantics of the additional KOOL constructs. */

/*@ \subsection{Configuration}
KOOL adds two nested cells to the configuration of SIMPLE.
The cell \textsf{crntObj} holds data pertaining to the current object,
that is, the object environment in which the code in cell
\textsf{k} executes: \textsf{crntClass} holds the current class (which
can change as methods of the current object are invoked );
\textsf{envStack} holds the stack of environments as a list,
each layer corresponding to one class in the objects' instance class
hierarchy; \textsf{location}, which is optional, holds the location in
the store where the current object is or has to be located (this is
useful both for method closures and for the semantics of object creation).
The cell \textsf{classes} holds all the declared classes, each class
being held in its own \textsf{class} cell which contains a name
(\textsf{className}), a parent (\textsf{extends}), and the actual
member declarations (\textsf{declarations}). */

  configuration <T color="red">
                  <threads color="orange">
                    <thread multiplicity="*" color="yellow">
                      <k color="green"> ($PGM:K ~> execute) </k>
                      <env color="violet"> .Map </env>
                      <holds color="black"> .Map </holds>
                      <br/>
                      <control color="cyan">
                        <fstack color="blue"> .List </fstack>
                        <xstack color="purple"> .List </xstack>
// KOOL addition
                        <br/>
                        <crntObj color="Fuchsia"> 
                           <crntClass> object </crntClass>
                           <envStack> .List </envStack>
                           <location multiplicity="?"> .K </location>
                        </crntObj>
                      </control>
                    </thread>
                  </threads>
                  <br/>
                  <store color="white"> .Map </store>
                  <busy color="cyan">.Set</busy>
                  <in color="magenta" stream="stdin"> .List </in>
                  <out color="brown" stream="stdout"> .List </out>
                  <nextLoc color="gray"> 0 </nextLoc>
// KOOL addition
                  <br/>
                  <classes color="Fuchsia">
                     <class multiplicity="*" color="Fuchsia">
                        <className color="Fuchsia"> main </className>
                        <extends color="Fuchsia"> object </extends>
                        <declarations color="Fuchsia"> .K </declarations>
                     </class>
                  </classes>
                </T>

/*@ \subsection{Unchanged Semantics from SIMPLE}
The semantics below is taken over from SIMPLE unchanged.
The semantics of function declaration and invocation, including the
use of the special \texttt{lambda} abstraction value, needs to change
in order to account for the fact that methods are now invoked into
their object's environment.  The semantics of function return actually
stays unchanged.  Also, the semantics of program initialization is
different: now we have to create an instance of the \texttt{main}
class which also calls the constructor \texttt{main()}, while in
SIMPLE we only had to invoke the function \texttt{main()}. 
Finally, the semantics of thread spawning needs to change, too: the
parent thread needs to also share its object environment with the
spawned thread (in addition to its local environment, like in SIMPLE).
This is needed in order to be able to spawn method invokations under
dynamic method dispatch; for example, ``\texttt{spawn run();}'' will
need to look up the method \texttt{run()} in the newly created thread,
operation which will most likely fail unless the child thread sees
the object environment of the parent thread.  Note that the
\texttt{spawn} statement of KOOL is more permissive than the threads
of Java.  In fact, the latter can be implemented in terms of
\texttt{spawn}---see the program \texttt{threads.kool} for a sketch.  */

  syntax Val ::= #Int | #Bool | #String
               | "arrayRef" "(" #Nat "," #Nat ")"
  syntax Vals ::= List{Val,","}

  syntax Exp ::= Val

  syntax KResult ::= Val

  syntax K ::= "undefined"  [:latex("\bot"):]

  rule <k> var X:#Id; => . ...</k>
       <env> Env:Map => Env[L:#Nat/X] </env>
       <store>... . => L|->undefined ...</store>
       <nextLoc> L => L +Nat 1 </nextLoc>

  rule <k> var X[N:#Nat]; => . ...</k>
       <env> Env => Env[L/X] </env>
       <store>... . => L |-> arrayRef(L +Nat 1, N)
                       L +Nat 1 .. L +Nat N |-> undefined ...</store>
       <nextLoc> L => L +Nat 1 +Nat N </nextLoc>

  context var X[[HOLE]];

  syntax #Id ::= "$1" | "$2"
  rule var X[N1,N2,Vs:Vals]; =>
       var X[N1];
       {
         var $1 = X;
         for $2 = 0 to _-_(N1,1) do   // stupid parser
         {
           (var X[N2,Vs];)            // stupid parser
           $1[$2] = X;
         }
       }  [:structural:]

  rule <k> X => V:Val ...</k>
       <env>...X|->L...</env>
       <store>...L|->V...</store> [:transition:]

  context ++([HOLE] => lvalue([HOLE]))
  rule <k> ++loc(L) => I:#Int +Int 1 ...</k>
       <store>... L |-> (I => I +Int 1) ...</store> [:transition:]

  rule I1:#Int + I2:#Int => I1 +Int I2
  rule Str1:#String + Str2:#String => Str1 +String Str2
  rule _-_(I1,I2) => _-Int_(I1,I2)
  rule I1 * I2 => I1 *Int I2
  rule I1 / I2 => I1 /Int I2 when I2 =/=Bool 0
  rule I1 % I2 => I1 %Int I2 when I2 =/=Bool 0
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

  rule V[N1,N2,Vs] => V[N1][N2,Vs]           [:structural:]
  rule arrayRef(L,_)[N] => lookup(L +Int N)  [:structural:]
  syntax K ::= "lookup" "(" #Nat ")"
  rule <k> lookup(L) => V ...</k> <store>...L|->V...</store>  [:transition:]

  rule sizeOf(arrayRef(_,N)) => N

/*@ The semantics of return, as well as the definition of
\texttt{bindto}, stay unchanged */
  rule <k> return(V); ~> _ => V ~> K </k>
       <control> <fstack> (Env,K,C) => . ...</fstack> (_ => C) </control>
       <env> _ => Env </env>
  syntax Val ::= "nothing"
  rule return; => return nothing;   [:structural:]

  syntax K ::= "bindto" "(" Ids "," Vals ")"
  rule <k> bindto((X,Xs => Xs),(V,Vs:Vals => Vs)) ...</k>
       <env> Env => Env[L/X] </env>
       <store>... . => L |-> V ...</store>
       <nextLoc> L => L +Nat 1 </nextLoc>
  rule <k> bindto(.Ids,.Exps) => . ...</k>  [:structural:]

  rule <k> read() => I ...</k> <in> ListItem(I) => . ...</in>    [:transition:]

  context ([HOLE] => lvalue([HOLE])) = _
  rule <k> loc(L)=V => V...</k> <store>...L|->(_=>V)...</store>  [:transition:]

  rule {} => . [:structural:]
  rule <k> {Ss:Stmts} => Ss~>env(Env) ...</k> <env> Env </env>   [:structural:]

  syntax K ::= "env" "(" Map ")"
  rule <k> env(Env) => . ...</k> <env> _ => Env </env>  [:structural:]

  rule (env(_) => .) ~> env(_)  [:structural:]

  rule S1:Stmt S2:Stmt => S1 ~> S2  [:structural:]

  rule V; => .

  rule if  true then S else _ => S
  rule if false then _ else S => S

  rule <k> while E:Exp do S
    => if E then {S while E do S} else {} ...</k> [:structural:]

  rule <k> print(V,Vs => Vs);...</k> <out>... . => ListItem(V) </out>
    [:transition:]
  rule print(.Vals); => .   [:structural:]

  syntax ListItem ::= "(" #Id "," Stmt "," K "," Map "," Bag ")"
  syntax K ::= "popx"
  rule <k> (try S1 catch(X) S2 => S1 ~> popx) ~> K </k>
       <control> <xstack> . => (X,S2,K,Env,C) ...</xstack> C:Bag </control>
       <env> Env </env>
  rule <k> popx => . ...</k> <xstack> _:ListItem => . ...</xstack>
  rule <k> throw V; ~> _ => {var X=V; S2} ~> K </k>
       <control> <xstack> (X,S2,K,Env,C) => . ...</xstack> (_ => C) </control>
       <env> _ => Env </env>

/*@ thread spawning needs a new semantics, but the other concurrency
constructs keep their semantics from SIMPLE. */
//  rule <thread>... <k> spawn S => . ...</k> <env> Env </env> ...</thread>
//       (. => <thread>... <k> S </k> <env> Env </env> ...</thread>)
  rule (<thread>... <k>.K</k> <holds> H:Map </holds> ...</thread> => .)
       <busy> Busy:Set => Busy -Set keys(H) </busy>
  rule <k> acquire V; => . ...</k> <holds>... . => V|->0 ...</holds>
       <busy> Busy (. => SetItem(V)) </busy>
    when notBool(V in Busy) [:transition:]
  rule <k> acquire V; => . ...</k> <holds>...V|->(N => N +Nat 1)...</holds>
  rule <k> release V; => . ...</k> <holds>...V|->(N => _-Int_(N,1))...</holds>
    when N >Nat 0
  // used prefix notation for -Int because of parsing problems
  rule <k> release V; => . ...</k> <holds>... V|->0 => . ...</holds>
       <busy>... SetItem(V)=>. ...</busy>
  rule <k> rendezvous V; => . ...</k>
       <k> rendezvous V; => . ...</k>  [:transition:]

  syntax Exp ::= "lvalue" "(" K ")"
  syntax Val ::= "loc" "(" #Nat ")"
  rule <k> lvalue(X) => loc(L:#Nat) ...</k>
       <env>... X|->L ...</env>  [:structural:]
  context lvalue(_[[HOLE]])
  context lvalue([HOLE][_])
  rule <k> lvalue(lookup(L)) => loc(L) ...</k>  [:structural:]

  syntax List{K} ::= #Nat ".." #Nat
  rule N1:#Nat..N2:#Nat => .List{K}              when N1  >Nat N2 [:structural:]
  rule N1:#Nat..N2:#Nat => N1 ,, (N1 +Nat 1)..N2 when N1 <=Nat N2 [:structural:]


/*@ \subsection{Changes to SIMPLE Semantics}
When we extend a language, sometimes we need to do more than just add
new language constructs and semantics for them.  Sometimes we want to
also extend the semantics of existing language constructs, in order to
get more from them. */

/*@ \subsubsection{Spawn}
In our case here, we want to extend the semantics of \texttt{spawn} to
also share the current object environment with the child thread, in
addition to the current environment.  This extension will allow us to
also use method invocations in the spawned statements, which will be
thus looked up as expected, using dynamic method dispatch.  This
lookup operation would fail if the child thread did not have access to
its parent's object environment. */

  rule <thread>... <k> spawn S => . ...</k>
                   <env> Env </env>
                   <crntObj> Obj </crntObj>
       ...</thread>
       (. => <thread>... <k> S </k>
                         <env> Env </env>
                         <crntObj> Obj </crntObj>
             ...</thread>)

//@ We next define the semantics of the additional KOOL features.

/*@ \subsection{Object and method closures}
We need to add two more values to the language, namely object and
method closures.  An object value consists of an
\texttt{objectClosure}-wrapped bag containing the current class of the
object and the environment stack of the object.  The current class of
an object will always be one of the classes mapped to an environment
in the environment stack of the object.  A method closure encapsulates
the method's parameters and code, as well as the object context in
which the method code should execute.  This object context includes
the current class of the object (the first argument of
\texttt{methodClosure}) and the object environment stack (located in
the object stored at the location specified as the second argument of
\texttt{methodClosure}). */

  syntax Val ::= "objectClosure" "(" Bag ")"
               | "methodClosure" "(" #Id "," #Nat "," Ids "," Stmt ")"

/*@ \subsection{Class declaration}
Initially, the classes forming the program are moved into their
corresponding cells: */

  rule <k> class Class1:#Id extends Class2:#Id { Ss:Stmts } => . <_/k>
       <classes>... (. => <class>
                            <className> Class1 </className>
                            <extends> Class2 </extends>
                            <declarations> Ss </declarations>
                        </class>)
       ...</classes>  [:structural:]

/*@ \subsection{Program initialization}
Once all the classes are processed as above, the computation item
\texttt{execute}, which was placed right after the program in the
initial configuration, is reached.  In SIMPLE, the program was
initialized by calling the method \texttt{main()}.  In KOOL, the
program is initialized by creating an object of class \texttt{main}.
This will also implicitly call the method \texttt{main()} (the
\texttt{main} class constructor).  The emptiness of the \textsf{env}
cell below is just a sanity check, to make sure that the user has not
declared anything but classes at the top level of the program. */

  syntax K ::= "execute"
  rule <k> execute => new main(); </k> <env> . </env>  [:structural:]

/*@ The semantics of \texttt{new} (defined shortly) requires the
execution of all the class' declarations (and also of its superclasses').
Field declarations are executed using the already existing semantics
of \texttt{var} from SIMPLE, but method declarations need a new
semantics.  This is defined next.  */

/*@ \subsection{Method declaration}
Like in SIMPLE, method names are added to the environment and bound
to their code.  However, unlike in SIMPLE where each method was
executed in the same environment, namely the program global
environment, a method in KOOL needs to be executed into its object's
environment.  Thus, methods evaluate to closures, which encapsulate
their object's context (i.e., the current class and environment stack
of the object) in addition to method's parameters and body.
This approach to bind method names to method closures in the
environment will also allow objects to pass their methods to other
objects, to dynamically change their methods by assigning them other
method closures, and even to allow all these to be done from other
objects.  This gives the KOOL programmer a lot of power; one should
use this power wisely, though, because programs can become easily
hard to understand and reason about if one overuses these features. */

  rule <k> method F:#Id(Xs:Ids) S:Stmt => . ...</k>
       <crntClass> Class:#Id </crntClass>
       <location> OL:#Nat </location>
       <env> Env => Env[L/F] </env>
       <store>... . => L|->methodClosure(Class,OL,Xs,S) ...</store>
       <nextLoc> L => L +Nat 1 </nextLoc>

/*@ \subsection{New}
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

  rule <k> new Class(Vs) ~> K 
        => create(Class) ~> storeObj ~> _`(_`)(Class,Vs); return this; </k>
       <env> Env => . </env>
       <control> C:Bag
         <crntObj> Obj
                => <crntClass> object </crntClass>
                   <envStack> ListItem(object::<env>.Map</env>) </envStack>
                   <location> L </location>
         </crntObj>
         <fstack> . => (Env, K, C <crntObj> Obj </crntObj>) ...</fstack>
       </control>
       <nextLoc> L => L +Nat 1 </nextLoc>

/*@ The creation of a new object (the memory allocation part only) is
a recursive process, requiring to first create an object for the
superclass.  A memory object representation is a layered structure:
for each class on the path from the instance class to the root of the
hierarchy there is a layer including the memory allocated for the
members (both fields and methods) of that class. */

  syntax K ::= "create" "(" K ")"

  rule <k> create(Class)
        => create(Class1) ~> setCrntClass(Class) ~> Ss ~> addEnvLayer ...</k>
       <className> Class </className>
       <extends> Class1 </extends>
       <declarations> Ss </declarations>  [:structural:]
  rule <k> create(object) => . ...</k>    [:structural:]

/*@ The next operation sets the current class of the current object.
This is necessary to be done at each layer, because the current class
of the object is enclosed as part of the method closures
(see the semantics of method declarations above). */

  syntax K ::= "setCrntClass" "(" #Id ")" 
  rule <k> setCrntClass(Class) => . ...</k>
       <crntClass> _ => Class </crntClass>  [:structural:]

/*@ The next operation adds a new tagged environment layer to the
current object and gets ready for the next layer by clearing the
environment (note that \texttt{create} expects the environment to be
empty). */

  syntax K ::= "addEnvLayer"
  rule <k> addEnvLayer => . ...</k>
       <env> Env => . </env>
       <crntClass> Class </crntClass>
       <envStack> . => ListItem(Class::<env>Env</env>) ...</envStack> 
    [:structural:]

/*@ The following operation stores the created object at the location
reserved by \texttt{new}.  Note that the location reserved by
\texttt{new} was temporarily stored in the \textsf{crntObj} cell
precisely for this purpose.  Now that the newly created object is
stored at its location and that all method closures are aware of it,
the location is unnecessary and thus we delete it from the
\textsf{crntObj} cell. */

  syntax K ::= storeObj
  rule <k> storeObj => . ...</k>
       <crntObj> Obj (<location> L </location> => .) </crntObj>
       <store>... . => L |-> objectClosure(Obj) ...</store>


/*@ \subsection{Self reference}
The semantics of \texttt{this} is straightforward: evaluate to the
current object. */

  rule <k> this => objectClosure(Obj) ...</k>  
       <crntObj> Obj </crntObj>


/*@ \subsection{Object member access}
We can access an object member (field or method) either explicitly,
using the construct \texttt{e.x}, or implicitly, using only the member
name \texttt{x} directly.  The borrowed semantics of SIMPLE will
already lookup a sole name in the local environment.  The first rule
below reduces implicit member access to explicit access when the name
cannot be found in the local environment.  There are two cases to
analyze for explicit object member access, depending upon whether the
object is a proper object or it is just a redirection to the parent
class via the construct \texttt{super}.  In the first case, we
evaluate the object expression and lookup the member starting with
current class (static scoping).  Note the use of the conditional
evaluation context.  In the second case, we just lookup the member
starting with the superclass of the current class.  In both cases,
the \texttt{lookupMember} task eventually yields a \texttt{lookup(L)}
task for some appropriate location \texttt{L}, which will be further
solved with the corresponding rule borrowed from SIMPLE.  Note that the
current object is not altered by \texttt{super}, so future method
invocations see the entire object, as needed for dynamic method dispatch. */

// To avoid parsing ambiguity, use _._(this,X) instead of this.X
  rule <k> X => _._(this,X) ...</k> <env> Env </env>
    when notBool(X in keys(Env))  [:structural:]

  context ('_._(`[HOLE`]:K,,_)) when (`[HOLE`]:K =/=Bool super)
  rule <k> _._(objectClosure(<crntClass> Class </crntClass>
                   <envStack>...ListItem(Class :: EnvC) EStack </envStack>),X)
        => lookupMember(<envStack>ListItem(Class :: EnvC) EStack</envStack>, X)
       ...</k>  [:structural:]

  rule <k> _._(super,X) => lookupMember(<envStack>EStack</envStack>, X)...</k>
       <crntClass> Class:#Id </crntClass>
       <envStack>... ListItem(Class :: EnvC) EStack </envStack>
    [:structural:]

/*@\subsection{Method invocation}
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

  rule <k> _`(_`)((X => V),_) ...</k>
       <env>... X |-> L ...</env>
       <store>... L |-> V ...</env>

  rule <k> _`(_`)((X => _._(this,X)),_) ...</k>
       <env> Env </env>
    when notBool(X in keys(Env))  [:structural:]

--- We would like to write the rule above as
---   rule <k> (X => _._(this,X))(_) <_/k>
--- or even
---   rule <k> (X => this.X)(_) <_/k>
--- but, unfortunately, our current Maude-based parser does not allow it
--- Same applies to other rules

  context '_`(_`)('_._(`[HOLE`]:K,,_),,_) when `[HOLE`]:K =/=Bool super 

  rule <k> '_`(_`)(('_._(objectClosure(Obj <envStack> EStack </envStack>),,X) 
        => lookupMember(<envStack> EStack </envStack>, X)),,_) ...</k>
    [:structural:]

  rule <k> '_`(_`)(('_._(super,,X) 
        => lookupMember(<envStack> EStack </envStack>, X)),,_) ...</k>
       <crntClass> Class:#Id </crntClass>
       <envStack>... ListItem(Class :: _) EStack </envStack>
    [:structural:]

  context '_`(_`)(`[HOLE`]:K,,_)
       when getKLabel `[HOLE`]:K ==Bool '_`(_`) orBool
          getKLabel `[HOLE`]:K ==Bool '_`[_`]

/*@ Eventually, each of the rules above produces a \texttt{lookup(L)}
task as a replacement for the method.  When that happens, we just
lookup the method closure at location \texttt{L}.  The semantics
of \texttt{methodClosure} is then as expected: the local environment
and control are stacked, then we switch to method closure's class and
object environment and execute the method body.  The \texttt{bindto}
construct is the one that came with the semantics of SIMPLE that we
borrowed (see above).  */

  rule <k> '_`(_`)((lookup(L) => V),,_) ...</k>
       <store>... L |-> V ...</store>

  syntax ListItem ::=  "(" Map "," K "," Bag ")"
  rule <k> _`(_`)(methodClosure(Class,OL:#Nat,Xs:Ids,S:Stmt), Vs:Vals) ~> K:K
        => bindto(Xs,Vs) ~> S ~> return; </k>
       <control> C:Bag
          <fstack> . => (Env,K,C <crntObj> Obj' </crntObj>) ...</fstack>
          <crntObj> Obj':Bag => <crntClass>Class</crntClass> Obj </crntObj>
        </control>
       <env> Env => . </env>
       <store>... OL |-> objectClosure(<crntClass>_:#Id</crntClass>Obj:Bag) 
       ...</store>


/*@ \subsection{Instance Of}
Searches the object environment for a layer corresponding to the
desired class.  It returns \texttt{true} iff it can find the class,
otherwise it returns \texttt{false}; it never gets stuck.  */

  rule objectClosure(_ <envStack>ListItem(Class::_)...</envStack>)
        instanceOf Class => true
  rule objectClosure(_ <envStack> ListItem(Class1::_)
                      => . ...</envStack>) instanceOf Class2 
    when Class1 =/=Bool Class2  [:structural:]
  rule objectClosure(_ <envStack> .List </envStack>) instanceOf Class
    => false
 
/*@ \subsection{Cast}
In untyped KOOL, we prefer to not check the validity of casting.  In
other words, any cast is allowed on any object, simply changing the
current class of the object to the desired class.  The execution will 
get stuck later if one attempts to access a field which is not
available.  Moreover, the execution may complete successfully even
in the presence of invalid casts, provided that each accessed member
during the current execution is, or happens to be, available.  */

  rule <k> cast objectClosure(<crntClass> _:K </crntClass> Obj) to Class
        => objectClosure(<crntClass> Class </crntClass> Obj) ...</k>

/*@ \subsection{Objects as lvalues}
The current machinery borrowed with the semantics of SIMPLE allows us
to enrich the set of lvalues, this way allowing new means to assign
values to locations.  In KOOL, we want object member names to be
lvalues, so that we can assign values to them using the already
existing machinery.  The first rule below ensures that the object is
always explicit, the evaluation context enforces the object to be
evaluated, and finally the second rule initiates the lookup for the
member's location based on the current class of the object. */

  rule <k> lvalue(X => _._(this,X)) <_/k> <env> Env </env>
    when notBool(X in keys(Env))  [:structural:]

  context lvalue(_._([HOLE],_))
  rule <k> lvalue(_._(objectClosure(<crntClass> Class </crntClass> 
                          <envStack>...
                            ListItem(Class :: EnvC) EStack
                          </envStack>), X)
        => lookupMember(<envStack>ListItem(Class :: EnvC:BagItem) EStack:List
                        </envStack>, X)) 
       ...</k>  [:structural:]
  
/*@ \subsection{Lookup member}
Searches for the given member in the given environment stack, starting
with the most concrete class and going up in the hierarchy. */

  syntax K ::= #Id "::" BagItem
  // Id is the class name, BagItem is its corresponding environment
  syntax K ::= "lookupMember" "(" BagItem "," #Id ")"  
  // BagItem is the envStack cell, Id is the member name

// First look for the member in the top environment; if found then done.
  rule lookupMember(<envStack> ListItem(_ :: <env>...X|->L...</env>)
                    ...</envStack>,X) => lookup(L)  [:structural:]
// Otherwise, recurse through the object environment stack
  rule lookupMember(<envStack> ListItem(_ :: <env> Env </env>)
                            => . ...</envStack>, X)
    when notBool(X in keys(Env))                      [:structural:]

end module
