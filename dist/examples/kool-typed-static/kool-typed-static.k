module KOOL-TYPED-STATIC-SYNTAX
  imports BUILTIN-SYNTAX-HOOKS

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

  syntax Id ::= "main"

  syntax Type ::= "int"
                | "bool"
                | "string"
                | "void"
                | "arrayOf" Type
                    [latex("{#1}\texttt{\char91\char93}")]
                | "function" "from" Types "to" Type
                    [latex("({#1}~\texttt{->}~{#2})")]

  syntax Types ::= List{Type,","}  [strict]

  syntax Decl ::= "var" Exps ";"

  syntax Exp ::= Int | Bool | String | Id
               | "this"
               | "super"
               | "(" Exp ")"            [bracket]
               | "++" Exp                
               | Exp "instanceOf" Id    [strict(1)]
               | "cast" Exp "to" Id     [strict(1)]
               | "new" Id "(" Exps ")"  [strict(2)]
               | Exp "." Id             [strict(1)]
//               | Exp ":" Type            // allowed only for declarations
               | Exp "of" Type           // allowed only for declarations
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


  syntax Exps ::= List{Exp,","}

  syntax Stmt ::= "{" "}"
                | "{" Stmts "}"
                | Exp ";"                           [strict]
                | "if" Exp "then" Stmt "else" Stmt  [avoid, strict]
                | "if" Exp "then" Stmt    
                | "while" Exp "do" Stmt             [strict]
                | "for" Id "=" Exp "to" Exp "do" Stmt
                | "return" Exp ";"                  [strict]
                | "return" ";"
                | "write" "(" Exp ")" ";"           [strict]
                | "try" Stmt "catch" "(" Exp ")" Stmt [strict(1)]
                | "throw" Exp ";"                   [strict]
                | "spawn" Stmt                      [strict] 
                | "acquire" Exp ";"                 [strict]
                | "release" Exp ";"                 [strict]
                | "rendezvous" Exp ";"              [strict]
                | "print" "(" Exps ")" ";"          [strict]


  syntax Stmts ::= Decl | Stmt
                 | Stmts Stmts            [seqstrict, right]

  rule E:Exp of T:Type => '_:_(E,, T) [anywhere]
  rule 'isExp('_:_(E:Exp,, T:Type)) => true [anywhere]

  rule if E:Exp then S:Stmt => if E then S else {}
  rule (for X:Id = E1:Exp to E2:Exp do S)
       =>
       {var X=E1, .Exps; while X <= E2 do {S X = (X + 1);}}

  rule var E1:Exp, E2:Exp, Es:Exps; => var E1, .Exps; var E2, Es;

  rule var '_:_(X:Id,, T:Type) = E:Exp, .Exps; => var '_:_(X,, T), .Exps; X = E;

/*@ \subsection{KOOL Additional Syntax}
Note the strictness attributes, telling which arguments need to be
typed before the actual construct can be typed. */

  syntax Id ::= "object"

  syntax Type ::= "class" Id
   
  syntax Decl ::= "method" Id "(" Exps ")" ":" Type Stmt
                | "method" Id "(" Exps ")" Stmt

  rule method X:Id (Es:Exps) S:Stmt => method X(Es) : void S

  syntax Decl ::= "class" Id "{" Stmts "}"
                | "class" Id "extends" Id "{" Stmts "}"

  rule 'class_`{_`}(C:Id,, Ss:Stmts ) => class C extends object { Ss }

endmodule 


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
//                  <br/>
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

  rule var (.Types); => stmt   [ structural]
  context var '_:_(_[HOLE],, _),.Exps;
  rule var '_:_(X[Ts:Types],, T), .Exps; => checkDepth(Ts,T) ~> var '_:_(X,, T);
       [structural]

  syntax K ::= "checkDepth" "(" Types "," Type ")"
  rule checkDepth((int,Ts => Ts), (arrayOf T => T))   [structural]
  rule checkDepth(.Types,_) => .K                     [structural]

/*@ Although functions turn into methods and get a slightly different
semantics, the \texttt{types(...)} operation stays the same. */

  syntax Types ::= "types" "(" Exps ")"   [function, klabel(types)]
  rule types(.Exps) => void, .Types       [anywhere]             
  rule types('_:_(X:Id,, T:Type), .Exps) => T, .Types   [anywhere]         
  rule types('_:_(X:Id,, T:Type), E:Exp, Es:Exps) => T, types(E,Es) [anywhere]

  rule <k> I:Int => int ...</k>
  rule <k> B:Bool => bool ...</k>
  rule <k> Str:String => string ...</k>

//@ Local type environment lookup also stays the same.

  rule <k> X:Id => T ...</k> <tenv>... X |-> T:Type ...</tenv>

  syntax Exp ::= "ltype" "(" Exp ")"
  rule ltype(X:Id) => X                   [structural]
  rule ltype(E:Exp[Es:Exps]) => E[Es]  [structural]

  context ++(HOLE => ltype(HOLE))
  rule ++ int => int
  rule int + int => int
  rule string + string => string
  rule '_-_(int,, int) => int
  rule int * int => int
  rule int / int => int
  rule int % int => int
  rule - int => int
  rule int < int => bool
  rule int <= int => bool
  rule int > int => bool
  rule int >= int => bool
  rule T:Type == T => bool
  rule T:Type != T => bool
  rule bool and bool => bool
  rule bool or bool => bool
  rule not(bool) => bool
  rule (arrayOf T:Type)[int,Ts:Types] => T[Ts]
  rule T:Type[(.Types)] => T
  rule sizeOf(arrayOf T:Type) => int
  rule read() => int
  context (HOLE => ltype(HOLE)) = _

  rule {} => stmt
/*@ Typing of blocks is the same as in statically typed SIMPLE,
although the function tasks are now called method tasks. */
  rule <task>
         <k> { Ss:Stmts } => stmt ...</k>
         <tenv> Rho:Map </tenv>
         Rest:Bag  // this ensures method task
       </task>
       (. => <task>
               <k> Ss </k>
               <tenv> Rho </tenv>
               Rest
             </task>)
  rule T:Type; => stmt
  rule if bool then stmt else stmt => stmt
  rule while bool do stmt  => stmt
  rule return; => stmt
  rule print(T:Type, Ts:Types => Ts);  when T ==K int orBool T ==K string
  rule print((.Types)); => stmt
  rule spawn stmt => stmt
  rule acquire T:Type; => stmt
  rule release T:Type; => stmt
  rule rendezvous_;(T:Type) => stmt

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

  rule <k> 'var_;('_`,_('_:_(X:Id,, T:Type),, .Exps))
            =>
            checkType(T) ~> stmt 
       ...</k>
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

  rule <k> var '_:_(X:Id,, T:Type); => checkType(T) ~> stmt ...</k>
       <ctenvT> Rho:Map (. => X |-> T) </ctenvT>
    when notBool(X in keys(Rho))

  rule <k> var '_:_(X:Id,, T:Type); => stuck(var '_:_(X,, T);) ...</k>
       <ctenvT>... X |-> _ ...</ctenvT>
       <inClass> C </inClass>
       <out>... . => ListItem("Member \"" +String Id2String(X)
                              +String "\" declared twice in class \""
                              +String Id2String(C) +String "\"!\n") </out>
    [structural]

/*@ \subsubsection{Assignment}
A more concrete value is allowed to be assigned to a more abstract
variable.  The operation \textsf{checkSubtype} is defined at the end
of the module and it also works with pairs of lists of types. */

  rule T:Type = T':Type => checkSubtype(T', T) ~> T

/*@ \subsubsection{}
Similarly, we allow values of more concrete types to be returned by
methods. */

  rule <k>
           return T:Type;
           =>
           checkSubtype(T,T') ~> stmt
       ...</k>
       <return> T' </return>


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
  rule <task>
          <k> class C:Id extends C':Id { Ss:Stmts }
              =>
              stmt
          ...</k>
       </task>
       (. => <class>...
               <className> C </className>
               <extends> C' </extends>
             ...</class>)
       (. => <task>
                <k> checkType(class C') ~> Ss:Stmts </k>
                <inClass> C </inClass>
                <tenv> . </tenv>
                <ctenvT> . </ctenvT>
             </task>)  [structural]

//@ \subsubsection{Check for unique class names}

// The rule below is also more complicated than needed because of the
// configuration abstraction which does not seem to work right.  We
// should not need to mention the classes cell.
  rule <T> (<classes>... <className> C:Id </className>
                         <className> C </className>
            ...</classes>
           _:Bag => .)
           <out>... . => ListItem("Class \"" +String Id2String(C)
                                  +String "\" declared twice!\n") </out>
       </T>  [structural]

/*@ \subsubsection{Check for cycles in class hierarchy}
We check for cycles in the class hierarchy by transitively closing the
class extends relation using the \textsf{extendsAll} cells, and
checking that a class will never appear in its own \texttt{extendsAll}
cell.  The first rule below initiates the transitive closure of the
superclass relation, the second transitively closes it, and the third
checks for cycles. */

  rule <extends> C:Id </extends>
       <extendsAll> . => SetItem(C) </extendsAll>  [structural]

  rule <class>...
         <extendsAll> SetItem(C:Id) Classes:Set (. => SetItem(C')) </extendsAll>
       ...</class>
       <class>...
         <className> C </className> <extends> C':Id </extends>
       ...</class>
    when notBool(C' in (SetItem(C) Classes))  [structural]

// similarly, we should not need to mention the classes cell below
  rule <T> (<classes>... <className> C:Id </className>
                         <extendsAll>...SetItem(C)...</extendsAll>
            ...</classes>
           _:Bag => .)
           <out>... . => ListItem("Class \"" +String Id2String(C)
                                  +String "\" is in a cycle!\n") </out>
       </T>  [structural]


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

  rule <k> method M:Id(XTs:Exps) : T:Type S:Stmt
        => checkMethod(M, function from types(XTs) to T, C')
           ~> var '_:_(M,, function from types(XTs) to T); ...</k>
       <inClass> C:Id </inClass>
       <ctenvT> _:Map </ctenvT> // to ensure we are in a class pass
       <className> C </className>
       <extends> C':Id </extends>
       (. => <task>
               <k> var XTs; S </k>
               <inClass> C </inClass>
               <tenv> .Map </tenv>
               <return> T </return>
             </task>)
    [structural]

/*@ The \texttt{checkMethod} operation below searches to see whether
the current method overrides some other method in some superclass.
If yes, then it issues an additional check that the new method's type
is more concrete than the overridden method's.  The types $T$ and $T'$
below can only be function types.  See the definition of
\texttt{checkSubtype} on function types at the end of this module (it
is co-variant in the codomain and contra-variant in the domain). */

  syntax K ::= "checkMethod" "(" Id "," Type "," Id ")"

  rule <k> checkMethod(M:Id, T:Type, C:Id) => checkSubtype(T, T') ...</k>
       <className> C </className>
       <ctenv>... M |-> T':Type ...</ctenv>
    [structural]

  rule <k> checkMethod(M:Id, T:Type, (C:Id => C')) ...</k>
       <className> C </className>
       <extends> C':Id </extends>
       <ctenv> Rho:Map </ctenv>
    when notBool(M in keys(Rho))
    [structural]

  rule checkMethod(_:Id,_,object) => .


/*@ \subsection{New}
To type \texttt{new} we only need to check that the class constructor
can be called with arguments of the given types, so we initiate a call
to the constructor method in the corresponding class.  If that
succeeds, meaning that it types to \texttt{stmt}, then we discard the
\texttt{stmt} type and produce instead the corresponding class type of
the new object.  The auxiliary \texttt{discard} operation is defined
also at the end of this module. */

  rule new C:Id(Ts:Types) => '_`(_`)('_._((class C),, C),, Ts) ~> discard ~> class C


/*@ \subsection{Self reference}
The typing rule for \texttt{this} is straightforward: reduce to the
current class type. */

  rule <k> this => class C ...</k>
       <inClass> C:Id </inClass>


/*@ \subsection{Super}
Similarly, \texttt{super} types to the parent class type.
Note that for typing concerns, super can be considered as an object 
(recall that this was not the case in the dynamic semantics). */

   rule <k> super => class C' ...</k>
        <inClass> C:Id </inClass>
        <className> C':Id </className>
        <extends> C':Id </extends>


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

  rule <k> X:Id => '_._(this,, X) ...</k>
       <tenv> Rho:Map </tenv>
       when notBool(X in keys(Rho))

  rule ltype('_._(E:Exp,, X:Id)) => '_._(E,, X)  [structural]

  rule <k> '_._(class C:Id,, X:Id) => T ...</k>
       <className> C </className>
       <ctenv>... X |-> T:Type ...</ctenv>

  rule <k> '_._(class (C1:Id => C2),, X:Id) ...</k>
       <className> C1 </className>
       <extends> C2:Id </extends>
       <ctenv> Rho:Map </ctenv>
    when notBool(X in keys(Rho))  [structural]

  rule <k> '_._(class object,, X:Id) => stuck('_._(class object,, X)) ...</k>
       <inClass> C:Id </inClass>
       <out>... . => ListItem("Member \"" +String Id2String(X)
                              +String "\" not declared! (see class \""
                              +String Id2String(C) +String "\")\n") </out>
    [structural]


/*@\subsection{Method invocation}
Methods can be applied on values of more concrete types than their
arguments.  The second rule below ensures that the empty list of
arguments is treated as a value of type \texttt{void}. */

  rule <k> '_`(_`)(function from Ts:Types to T:Type,, (T':Type,Ts':Types))
           => checkSubtype((T',Ts'),Ts) ~> T 
       ...</k>

  rule '_`(_`)(function from void to T:Type,, .Types) => T


/*@ \subsection{Instance of and casting}
As it is hard to check statically whether casting is always safe,
the programmer is simply trusted from a typing perspective.  Dynamic
semantics or implementations of the language may insert a runtime
check for the casting. */

  rule  (class C1:Id) instanceOf C2:Id => bool
  rule cast (class C1) to C2 => (class C2) 


/*@ \subsection{Exceptions}
Exceptions can throw and catch only class types.  Since unlike in Java
KOOL's methods do not declare the exception types that they can throw,
we cannot test the full type safety of exceptions.  Instead, we
only check that the \texttt{try} and the \texttt{catch} statements
type correctly. */

  rule try stmt catch('_:_(X:Id,, class C:Id)) S:Stmt => {var '_:_(X,, class C); S}
    [structural]
  rule throw class _:Id ; => stmt


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

  rule <task> <k> stmt => new main(.Exps); </k>
              (. => <tenv> . </tenv>
                    <return> void </return>
                    <inClass> main </inClass>)
       </task>
    [structural]

// discard class task when done, adding a ctenv in class

  rule (<task>
          <k> stmt </k>
          <ctenvT> Rho:Map </ctenvT>
          <inClass> C:Id </inClass>
        </task> => .)
        <className> C </className>
        (. => <ctenv> Rho </ctenv>)
    [structural]

// discard method task when done
  rule <task>...
         <k> stmt </k>
         <tenv> _:Map </tenv>  // only to ensure that this is a method task
       ...</task> => .
    [structural]

// cleanup tasks and output a success message when done
  rule (<tasks> .Bag </tasks> => .)
       <out>... . => ListItem("All typing tasks completed.\n") </out>
    [structural]



//@\subsection{Auxiliary operations}

/*@\subsection{Subtyping constraints}
The subclass relation introduces a subtyping relation.  
*/
  syntax K ::= "checkSubtype" "(" Types "," Types ")"

  rule checkSubtype(.Types, .Types) => .
  rule checkSubtype((T1:Type, T2:Type, Ts:Types), (T1':Type,T2':Type,Ts':Types))
    => checkSubtype(T1, T1') ~> checkSubtype((T2, Ts), (T2', Ts'))
  rule checkSubtype(T:Type, T) => .
  rule <k> checkSubtype(class C1:Id, class C:Id)
           => checkSubtype(class C2, class C) 
       ...</k>
       <className> C1 </className>
       <extends> C2:Id </extends>
       when C1 =/=K C

  rule checkSubtype(function from Ts:Types to T:Type, function from Ts':Types to T':Type)
       =>
       checkSubtype((T,Ts'),(T',Ts))


/*@  Since now any id can be used as the type of a class, we need to check
that the types used in the program actually exists */
  syntax K ::= "checkType" "(" Types ")" 

  rule checkType(T:Type, T':Type,Ts:Types) => checkType(T) ~> checkType(T',Ts)
  rule checkType(.Types) => .
  rule checkType(int) => .
  rule checkType(bool) => .
  rule checkType(string) => .
  rule checkType(void) => .
  rule <k> checkType(class C:Id) => . ...</k> <className> C </className>
  rule checkType(class object) => .
  rule checkType(function from Ts:Types to T:Type) => checkType(T,Ts)
  rule checkType(arrayOf T:Type) => checkType(T)


//@ These should be generic, belonging to the K framework
  syntax K ::= "stuck" "(" K ")"  [latex("\framebox{${#1}$}")]
  syntax K ::= "discard"
  rule _:KResult ~> discard => .  [structural]

  rule Id2String(main) => "main"

endmodule


