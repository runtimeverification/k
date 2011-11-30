module KOOL-TYPED-STATIC-SYNTAX

/*@ \section{Syntax}
The syntax of statically typed KOOL is identical to that of
dynamically typed KOOL, they both taking as input the same programs.
What differs is the \K strictness attributes.  Like in statically
typed KOOL, almost all language constructs are strict now, since we
want each to type its arguments almost all the time.  Like in the
other two KOOL definitions, we prefer to first list the syntax
borrowed unchanged from SIMPLE and then add the KOOL new constructs. */

/*@ \subsection{Syntax from SIMPLE}
The syntax below is taken over unchanged from SIMPLE, including all
the \K strictness attributes and the desugaring macros. */

  syntax #Id ::= "main"

  syntax Type ::= "int"
                | "bool"
                | "string"
                | "void"
                | "arrayOf" Type
                    [:prec(1) latex "{#1}\texttt{\char91\char93}":]
                | "function" "from" Types "to" Type
                    [:prec(1) latex "({#1}\ \texttt{->}\ {#2})":]
  syntax Types ::= List{Type,","}

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
               | Exp "(" Exps ")"      [:strict prec(2):]
               | "read" "(" ")"
               | Exp "=" Exp           [:strict(2) prec(40) gather (e E):]
               | Exp ":" Type          [:prec(10):]
                                       // allowed only for declarations
  syntax Exps ::= List{Exp,","}

  syntax Stmt ::= "{" "}"
                | "{" Stmts "}"
                | Exp ";"                               [:strict prec(45):]
                | "if" Exp "then" Stmt "else" Stmt      [:strict prec(90):]
                | "if" Exp "then" Stmt                  [:prec(89):]
                | "while" Exp "do" Stmt                 [:strict prec(90):]
                | "for" #Id "=" Exp "to" Exp "do" Stmt  [:prec(90):]
                | "return" Exp ";"                      [:strict:]
                | "return" ";"
                | "print" "(" Exps ")" ";"              [:strict:]
                | "throw" Exp ";"                       [:strict:]
                | "spawn" Stmt                          [:strict prec(90):]
                | "acquire" Exp ";"                     [:strict:]
                | "release" Exp ";"                     [:strict:]
                | "rendezvous" Exp ";"                  [:strict:]

  syntax Stmts ::= Decl | Stmt
                 | Stmts Stmts            [:seqstrict prec(100) gather(e E):]

  macro if E:Exp then S:Stmt = if E then S else {}
  macro (for X = E1 to E2 do S) = {var X:int=E1; while X <= E2 do {S X=X+1;}}
  macro var E1:Exp, E2:Exp, Es:Exps; = var E1; var E2, Es;
  macro var X:#Id : T:Type = E; = var X : T; X = E;


/*@ \subsection{KOOL Additional Syntax}
Note the strictness attributes, telling which arguments need to be
typed before the actual construct can be typed. */

  syntax #Id ::= "object"

  syntax Type ::= "class" #Id [prec 1]
   
  syntax Decl ::= "method" #Id "(" Exps ")" ":" Type Stmt
                | "method" #Id "(" Exps ")" Stmt
  macro method X:#Id (Es:Exps) S:Stmt = method X(Es) : void S

  syntax Decl ::= "class" #Id "{" Stmts "}"
                | "class" #Id "extends" #Id "{" Stmts "}"
  macro class C:#Id {Ss:Stmts} = class C extends object {Ss}

  syntax Exp ::= "new" #Id "(" Exps ")" [:strict(2) prec(1):]
               | "this"
               | "super"
               | Exp "." #Id            [:prec(1) strict(1):]
               | Exp "instanceOf" #Id   [:prec(0) strict(1):]
               | "cast" Exp "to" #Id    [:prec(0) strict(1):]

  syntax Stmt ::= "try" Stmt "catch" "(" Exp ")" Stmt   [:strict(1) prec(90):]
end module 


module KOOL-TYPED-STATIC
  imports KOOL-TYPED-STATIC-SYNTAX

/*@ \section{Static semantics}
We first discuss the configuration, then give the static semantics
taken over unchanged from SIMPLE, then discuss the static semantics of
SIMPLE syntactic constructs that needs to change, and in the end we
discuss the static semantics and additional checks specifically
related to the KOOL proper syntax. */

/*@ \subsection{Configuration}
The configuration of our type system consists of a \textsf{tasks}
cell and of an \textsf{out} cell with the same meaning like in
statically typed SIMPLE, plus a cell \texttt{classes} holding data
about each class in a separate \textsf{class} cell.  The \textsf{task}
cells now have two additional optional subcells, namely
\textsf{ctenvT} and \textsf{inClass}.  The former holds a temporary
class type environment; its contents will be transferred into the
\textsf{ctenv} cell of the corresponding class as soon as all the
fields and methods in the task are processed.  In fact, there will be
three types of tasks in the subsequent semantics, each determined by
the subset of cells that it holds:
\begin{enumerate}
\item {\em Main task}, holding only a \textsf{k} cell holding the
original program as a set of classes.  The role of this task is to
process each class, generating a class task (see next) for each.
\item {\em Class task}, holding \textsf{k}, \textsf{ctenvT}, and
\textsf{inClass} subcells.  The role of this task type is to process
a class' contents, generating a class type environment in the
\textsf{ctenvT} cell and a method task (see next) for each method in
the class.  To avoid interference with object member lookup rules
below, it is important to add the class type environment to a class
atomically; this is the reason for which we use \textsf{ctenvT}
temporary cells within class tasks (instead of adding each member
incrementally to the class' type environment).
\item {\em Method task}, holding \textsf{k}, \textsf{tenv} and
\textsf{return} cells.  These tasks are similar to SIMPLE's function
tasks, so we do not discuss them here any further.
\end{enumerate}
Each \textsf{class} cell hods its name (in the \textsf{className}
cell) and the name of the class it extends (in the \textsf{extends}
cell), as well as its type environment (in the \textsf{ctenv} cell)
and the set of all its superclasses (in the \textsf{extendsAll} cell).
The later is useful for checking whether there are cycles in the
class extends relation. */

  configuration <T color="red">
                  <tasks color="orange">
                    <task multiplicity="*" color="yellow">
                      <k color="green"> $PGM:Stmts </k>
                      <tenv multiplicity="?" color="cyan"> .Map </tenv>
                      <ctenvT multiplicity="?" color="blue"> .Map </ctenvT>
                      <return multiplicity="?"> .K </return>
                      <inClass multiplicity="?" color="Fuchsia"> .K </inClass>
                    </task>
                  </tasks>
                  <br/>
                  <classes color="Fuchsia">
                    <class multiplicity="*">
                      <className color="Fuchsia"> object </className>
                      <extends color="Fuchsia"> .K </extends>
                      <extendsAll color="Fuchsia"> .Set </extendsAll>
                      <ctenv multiplicity="?" color="blue"> .Map </ctenv>
                    </class>
                  </classes>
                  <out color="brown" stream="stdout"> .List </out>
                </T>

/*@ \subsection{Static semantics from SIMPLE}
The syntax and rules below are borrowed unchanged from statically
typed SIMPLE, so we do not discuss them much here. */

  syntax Exp ::= Type
  syntax Stmt ::= Type
  syntax KResult ::= Type
  
  syntax Type ::= "stmt"

  rule var .Types; => stmt   [: structural:]
  context var _[[HOLE]] : _;
  rule var X[Ts:Types] : T; => checkDepth(Ts,T) ~> var X : T;  [:structural:]
  syntax K ::= "checkDepth" "(" Types "," Type ")"
  rule checkDepth((int,Ts => Ts), (arrayOf T => T))   [:structural:]
  rule checkDepth(.Types,_) => .K                     [:structural:]

/*@ Although functions turn into methods and get a slightly different
semantics, the \texttt{types(...)} operation stays the same. */

  syntax Types ::= "types" "(" Exps ")"                [:prec(1):]
  rule types(.Exps) => void,.Types                     [:structural:]
  rule types(X : T) => T,.Types                        [:structural:]
  rule types(X : T, E:Exp, Es:Exps) => T, types(E,Es)  [:structural:]

  rule <k> I:#Int => int ...</k>
  rule <k> B:#Bool => bool ...</k>
  rule <k> Str:#String => string ...</k>

//@ Local type environment lookup also stays the same.

  rule <k> X => T ...</k> <tenv>... X |-> T ...</tenv>

  syntax Exp ::= "ltype" "(" Exp ")"
  rule ltype(X) => X                   [:structural:]
  rule ltype(E:Exp[Es:Exps]) => E[Es]  [:structural:]

  context ++([HOLE] => ltype([HOLE]))
  rule ++ int => int
  rule int + int => int
  rule string + string => string
  rule _-_(int,int) => int
  rule int * int => int
  rule int / int => int
  rule int % int => int
  rule - int => int
  rule int < int => bool
  rule int <= int => bool
  rule int > int => bool
  rule int >= int => bool
  rule T == T => bool
  rule T != T => bool
  rule bool and bool => bool
  rule bool or bool => bool
  rule not(bool) => bool
  rule (arrayOf T)[int,Ts] => T[Ts]
  rule T[.Types] => T
  rule sizeOf(arrayOf T) => int
  rule read() => int
  context ([HOLE] => ltype([HOLE])) = _

  rule {} => stmt
/*@ Typing of blocks is the same as in statically typed SIMPLE,
although the function tasks are now called method tasks. */
  rule <task>
         <k> {Ss:Stmts} => stmt ...</k>
         <tenv> Rho </tenv> Rest:Bag  // this ensures method task
       </task>
       (. => <task>
               <k> Ss:Stmts </k>
               <tenv> Rho </tenv> Rest:Bag
             </task>)
  rule T; => stmt
  rule if bool then stmt else stmt => stmt
  rule while bool do stmt  => stmt
  rule return; => stmt
  rule print(T,Ts => Ts);  if T ==Bool int orBool T ==Bool string
  rule print(.Types); => stmt
  rule spawn stmt => stmt
  rule acquire T; => stmt
  rule release T; => stmt
  rule rendezvous_;(T) => stmt

  rule stmt stmt => stmt

/*@ \subsection{Changes to SIMPLE static semantics}
Below we give the new static semantics for language constructs that
come from SIMPLE, but whose SIMPLE static semantics was too
restrictive or too permissive and thus had to change. */

/*@ \subsubsection{Local variable declaration}
Since we can define new types in KOOL (corresponding to classes), the
variable declaration needs to now check that the claimed types exist.
The operation \texttt{checkType}, defined at the end of this module,
checks whether the argument type is correct (it actually works with
lists of types as well). */

  rule <k> var X:#Id : T:Type; => checkType(T) ~> stmt ...</k>
       <tenv> Rho:Map => Rho[T / X] </tenv>

/*@ \subsubsection{Class member declaration}
In class tasks, variable declarations mean class member declarations.
Since we reduce method declarations to variable declarations (see
below), a variable declaration in a class task can mean either a field
or a method declaration.  Unlike local variable declarations, which
can shadow previous homonymous local or member declarations, member
declarations are regarded as a set, so we disallow multiple
declarations for the same member (one could improve upon this, like in
Java, by treating members with different types or number of arguments
as different, etc., but we do not do it here).  We also issue an error
message if one attempts to redeclare the same class member.  The
framed variable declaration in the second rule below should be read
``stuck''.  In fact, it is nothing but a unary operation called
\texttt{stuck}, which takes a \K-term as argument and does nothing
with it; this \texttt{stuck} operation is displayed as a frame in this
PDF document because of its latex attribute (see the ASCII .k file,
at the end of this module). */

  rule <k> var X : T ; => checkType(T) ~> stmt ...</k>
       <ctenvT> Rho (. => X|->T) </ctenvT>
    if notBool(X in keys(Rho))

  rule <k> var X : T; => stuck(var X : T;) ...</k>
       <ctenvT>... X|->_ ...</ctenvT>
       <inClass> C </inClass>
       <out>... . => ListItem("Member \"" +String Id2String(X)
                              +String "\" declared twice in class \""
                              +String Id2String(C) +String "\"!\n") </out>
    [:structural:]

/*@ \subsubsection{Assignment}
A more concrete value is allowed to be assigned to a more abstract
variable.  The operation \textsf{checkSubtype} is defined at the end
of the module and it also works with pairs of lists of types. */

  rule T=T':Type => checkSubtype(T', T) ~> T

/*@ \subsubsection{}
Similarly, we allow values of more concrete types to be returned by
methods. */

  rule <k> return T;
    => checkSubtype(T,T') ~> stmt ...</k> <return> T' </return>


//@ We now move to the specific KOOL constructs.

/*@ \subsection{Class declaration}
We process each class in the main task, adding the corresponding data
into its \textsf{class} cell and also adding a class task for it.  We
also perform some well-formedness checks on the class hierarchy. */

/*@ \subsubsection{Initiate class processing}
We create a class cell and a class task for each task.  Also, we start
the class task with a check that the class it extends is declared
(this delays the task until that class is processed using another
instance of this rule). */

// There seems to be some error with the configuration concretization,
// as the rule below does not work when rewriting . to both the task
// and the class cells; I had to include two separate . rewrites
  rule <task> <k> class C:#Id extends C':#Id { Ss:Stmts }
               => stmt ...</k> </task>
       (. => <class>...
               <className> C </className>
               <extends> C' </extends>
             ...</class>)
       (. => <task>
                <k> checkType(class C') ~> Ss:Stmts </k>
                <inClass> C </inClass>
                <ctenvT> . </ctenvT>
             </task>)  [:structural:]

//@ \subsubsection{Check for unique class names}

// The rule below is also more complicated than needed because of the
// configuration abstraction which does not seem to work right.  We
// should not need to mention the classes cell.
  rule <T> (<classes>... <className> C </className>
                         <className> C </className>
            ...</classes>
           _:Bag => .)
           <out>... . => ListItem("Class \"" +String Id2String(C)
                                  +String "\" declared twice!\n") </out>
       </T>  [:structural:]

/*@ \subsubsection{Check for cycles in class hierarchy}
We check for cycles in the class hierarchy by transitively closing the
class extends relation using the \textsf{extendsAll} cells, and
checking that a class will never appear in its own \texttt{extendsAll}
cell.  The first rule below initiates the transitive closure of the
superclass relation, the second transitively closes it, and the third
checks for cycles. */

  rule <extends> C </extends>
       <extendsAll> . => SetItem(C) </extendsAll>  [:structural:]

  rule <class>...
         <extends> C </extends>
         <extendsAll> Classes:Set (. => SetItem(C')) </extendsAll>
       ...</class>
       <class>...
         <className> C </className> <extends> C' </extends>
       ...</class>
    if notBool(C' in Classes)  [:structural:]

// similarly, we should not need to mention the classes cell below
  rule <T> (<classes>... <className> C </className>
                         <extendsAll>...SetItem(C)...</extendsAll>
            ...</classes>
           _:Bag => .)
           <out>... . => ListItem("Class \"" +String Id2String(C)
                                  +String "\" is in a cycle!\n") </out>
       </T>  [:structural:]


/*@ \subsection{Method declaration}
A method declaration requires two conceptual checks to be performed:
first, that the method's type is consistent with the type of the
homonymous method that it overrides, if any; and second, that it body
types correctly.  At the same time, it should also be added to the
type environment of its class.  The first conceptual task is performed
using the \texttt{checkMethod} operation defined below, and the second
by generating a corresponding method task.  To add it to the class
type environment, we take advantage of the fact that KOOL is higher
order and reduce the problem to a field declaration problem, which we
have already defined.  The role of the \textsf{ctenvT} cell in the
rule below is to structurally ensure that the method declaration takes
place in a class task (we do not want to allow methods to be declared,
for example, inside other methods). */

  rule <k> method M:#Id(XTs:Exps) : T S:Stmt
        => checkMethod(M, function from types(XTs) to T, C')
           ~> var M : function from types(XTs) to T; ...</k>
       <inClass> C </inClass>
       <ctenvT> _:Map </ctenvT> // to ensure we are in a class pass
       <className> C </className>
       <extends> C' </extends>
       (. => <task>
               <k> var XTs; S </k>
               <inClass> C </inClass>
               <tenv> .Map </tenv>
               <return> T </return>
             </task>)
    [:structural:]

/*@ The \texttt{checkMethod} operation below searches to see whether
the current method overrides some other method in some superclass.
If yes, then it issues an additional check that the new method's type
is more concrete than the overridden method's.  The types $T$ and $T'$
below can only be function types.  See the definition of
\texttt{checkSubtype} on function types at the end of this module (it
is co-variant in the codomain and contra-variant in the domain). */

  syntax K ::= "checkMethod" "(" #Id "," Type "," #Id ")"

  rule <k> checkMethod(M,T,C) => checkSubtype(T,T') ...</k>
       <className> C </className>
       <ctenv>... M |-> T' ...</ctenv>
    [:structural:]

  rule <k> checkMethod(M,T,(C => C')) ...</k>
       <className> C </className>
       <extends> C' </extends>
       <ctenv> Rho </ctenv>
    if notBool(M in keys(Rho))
    [:structural:]

  rule checkMethod(_,_,object) => .


/*@ \subsection{New}
To type \texttt{new} we only need to check that the class constructor
can be called with arguments of the given types, so we initiate a call
to the constructor method in the corresponding class.  If that
succeeds, meaning that it types to \texttt{stmt}, then we discard the
\texttt{stmt} type and produce instead the corresponding class type of
the new object.  The auxiliary \texttt{discard} operation is defined
also at the end of this module. */

  rule new C(Ts) => _`(_`)(_._((class C), C), Ts) ~> discard ~> class C


/*@ \subsection{Self reference}
The typing rule for \texttt{this} is straightforward: reduce to the
current class type. */

  rule <k> this => class C ...</k>
       <inClass> C </inClass>


/*@ \subsection{Super}
Similarly, \texttt{super} types to the parent class type.
Note that for typing concerns, super can be considered as an object 
(recall that this was not the case in the dynamic semantics). */

   rule <k> super => class C' ...</k>
        <inClass> C </inClass>
        <className> C </className>
        <extends> C' </extends>


/*@ \subsection{Object member access}
There are several cases to consider here.  First, we should redirect
variable lookups to member accesses when the variable is not local
(the local variables are handled by the rule borrowed from SIMPLE).
This is what the first rule below does.  Second, we should allow
object member accesses as lvalues, which is done by the second rule
below.  These two rules therefore ensure that each necessary object
member access is explicitly allowed for evaluation.  Recall from the
annotated syntax module above that the member access operation is
strict in the object.  That means that that the object is expected to
evaluate to a class type.  The next two rules below define the actual
member lookup operation, moving the search to the superclass when the
member is not found in the current class.  Note that this works
because we create the class type environments atomically; thus, a
class either has its complete type environment available, in which
case these rules can safely apply, or its cell \textsf{ctenv} is not
yet available, in which case these rules have to wait.  Finally, the
fifth rule below reports an error when the \texttt{object} class is
reached. */

  rule <k> X => _._(this,X) ...</k> <tenv> Rho </tenv>
    if notBool(X in keys(Rho))

  rule ltype(_._(E,X)) => _._(E,X)  [:structural:]

  rule <k> _._(class C,X) => T ...</k>
       <className> C </className> <ctenv>... X |-> T ...</ctenv>

  rule <k> _._(class (C1 => C2),X) ...</k>
       <className> C1:#Id </className> <extends> C2:#Id </extends>
       <ctenv> Rho </ctenv>
    if notBool(X in keys(Rho))  [:structural:]

  rule <k> _._(class object,X) => stuck(_._(class object,X)) ...</k>
       <inClass> C </inClass>
       <out>... . => ListItem("Member \"" +String Id2String(X)
                              +String "\" not declared! (see class \""
                              +String Id2String(C) +String "\")\n") </out>
    [:structural:]


/*@\subsection{Method invocation}
Methods can be applied on values of more concrete types than their
arguments.  The second rule below ensures that the empty list of
arguments is treated as a value of type \texttt{void}. */

  rule <k> _`(_`)(function from Ts to T, Ts':Types)
        => checkSubtype(Ts',Ts) ~> T ...</k>
  rule _`(_`)(function from void to T, .Types) => T


/*@ \subsection{Instance of and casting}
As it is hard to check statically whether casting is always safe,
the programmer is simply trusted from a typing perspective.  Dynamic
semantics or implementations of the language may insert a runtime
check for the casting. */

  rule  (class C1:#Id) instanceOf C2:#Id => bool
  rule cast (class C1) to C2 => (class C2) 


/*@ \subsection{Exceptions}
Exceptions can throw and catch only class types.  Since unlike in Java
KOOL's methods do not declare the exception types that they can throw,
we cannot test the full type safety of exceptions.  Instead, we
only check that the \texttt{try} and the \texttt{catch} statements
type correctly. */

  rule try stmt catch(X : class C) S => {var X : class C; S}
    [:structural:]
  rule throw class _; => stmt


/*@ \subsection{Cleanup tasks}
Finally, we need to clean up the terminated tasks.  Each of the three
types of tasks is handled differently.  The main task is replaced by a
method task holding ``\texttt{new main();}'', which will ensure that a
\texttt{main} class with a \texttt{main()} method actually exists
(first rule below).  A class task moves its temporary class type
environment into its class' cell, and then it dissolves itself (second
rule).  A method task simply dissolves when terminated (third rule);
the presence of the \textsf{tenv} cell in that rule ensures that that
task is a method task.
Finally, when all the tasks are cleaned up, we can also remove the
\textsf{tasks} cell, issuing a corresponding message.  Note that
checking for cycles or duplicate methods can still be performed after
the \textsf{tasks} cell has been removed. */

// discard main task when done, issuing a "new main();" command to
// make sure that the class main and the method main() are declared.

  rule <task> <k> stmt => new main(); </k>
              (. => <tenv> . </tenv>
                    <return> void </return>
                    <inClass> main </inClass>)
       </task>
    [:structural:]

// discard class task when done, adding a ctenv in class

  rule (<task>
          <k> stmt </k>
          <ctenvT> Rho </ctenvT>
          <inClass> C </inClass>
        </task> => .)
        <className> C </className>
        (. => <ctenv> Rho </ctenv>)
    [:structural:]

// discard method task when done
  rule <task>...
         <k> stmt </k>
         <tenv>_:Map</tenv>  // only to ensure that this is a method task
       ...</task> => .
    [:structural:]

// cleanup tasks and output a success message when done
  rule (<tasks> .Bag </tasks> => .)
       <out>... . => ListItem("All typing tasks completed.\n") </out>
    [:structural:]



//@\subsection{Auxiliary operations}

/*@\subsection{Subtyping constraints}
The subclass relation introduces a subtyping relation.  
*/
  syntax K ::= "checkSubtype" "(" Types "," Types ")"

  rule checkSubtype(.Types,.Types) => .
  rule checkSubtype((T1:Type,T2:Type,Ts),(T1':Type,T2':Type,Ts':Types))
    => checkSubtype(T1,T1') ~> checkSubtype((T2,Ts),(T2',Ts'))
  rule checkSubtype(T,T) => .
  rule <k> checkSubtype(class C1, class C)
        => checkSubtype(class C2, class C) ...</k>
          <className> C1 </className> <extends> C2 </extends>
    if C1 =/=Bool C
  rule checkSubtype(function from Ts to T, function from Ts' to T')
    => checkSubtype((T,Ts'),(T',Ts))


/*@  Since now any id can be used as the type of a class, we need to check
that the types used in the program actually exists */
  syntax K ::= "checkType" "(" Types ")" 

  rule checkType(T,T',Ts) => checkType(T) ~> checkType(T',Ts)
  rule checkType(.Types) => .
  rule checkType(int) => .
  rule checkType(bool) => .
  rule checkType(string) => .
  rule checkType(void) => .
  rule <k> checkType(class C) => . ...</k> <className> C </className>
  rule checkType(class object) => .
  rule checkType(function from Ts to T) => checkType(T,Ts)
  rule checkType(arrayOf T) => checkType(T)


//@ These should be generic, belonging to the K framework
  syntax K ::= "stuck" "(" K ")"  [:latex "\framebox{${#1}$}":]
  syntax K ::= "discard"
  rule _:KResult ~> discard => .  [:structural:]

end module


