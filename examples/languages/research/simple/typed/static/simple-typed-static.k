
module SIMPLE-TYPED-STATIC-SYNTAX

/*@ \section{Syntax}
The syntax of typed SIMPLE extends that of untyped SIMPLE with support
for declaring types to variables and functions. */

  syntax #Id ::= "main"

/*@ \subsection{Types}
Primitive, array and function types, as well as lists (or tuples) of types.
The lists of types are useful for function arguments. */

  syntax Type ::= "int"
                | "bool"
                | "string"
                | "void"
                | "arrayOf" Type
                    [:prec(1) latex "{#1}\texttt{\char91\char93}":]
                | "function" "from" Types "to" Type
                    [:prec(1) latex "({#1}\ \texttt{->}\ {#2})":]
  syntax Types ::= List{Type,","}

/*@ \subsection{Declarations}
Variable and function declarations are allowed to have a more generous
syntax than how we want them to be used in programs, but the type
system will be defined in such a way that all abuses will be caught.
For example, functions will only be allowed to take typed identifiers
as parameters.  The reason we prefer to allow a more generous syntax is
to simplify our overall syntax by defining fewer syntactic categories.
Recall that, after all, the syntax defined in \K is what we call ``the
syntax of the semantics'', that is, some syntax which is convenient
enough to write the desired semantic rules.  This syntax is not meant
to be used to parse complex programming language, such as C or Java.
While \K's syntax is good enough to parse simple and pedagogical
languages like this one, in practice you are expected to use external
parsers for complex languages. */

  syntax Decl ::= "var" Exps ";"
                | "function" #Id "(" Exps ")" ":" Type Stmt

/*@ \subsection{Expressions}
The syntax of expressions is identical to that in untyped SIMPLE,
except for the last construct in the sequence below.  That is allowed
exclusively only for parsing declarations, as described above.  It
will be given no semantics. */

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

/*@ \subsection{Statements}
The statements have the same syntax as in untyped SIMPLE.  That is
because we decided that counters in \texttt{for} loops and thrown
exceptions can only be integers, so there is no need to declare them.
Note that, unlike in untyped SIMPLE, all statement constructs which
have arguments and are not desugared are strict, including the
conditional and the \texttt{while}.  Indeed, from a typing
perspective, they are all strict: first type their arguments and then
type the actual construct. */

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
                | "try" Stmt "catch" "(" #Id ")" Stmt   [:strict(1) prec(90):]
                | "throw" Exp ";"                       [:strict:]
                | "spawn" Stmt                          [:strict prec(90):]
                | "acquire" Exp ";"                     [:strict:]
                | "release" Exp ";"                     [:strict:]
                | "rendezvous" Exp ";"                  [:strict:]

  syntax Stmts ::= Decl | Stmt
                 | Stmts Stmts            [:seqstrict prec(100) gather(e E):]

/*@ We use the same desugaring macros like in untyped SIMPLE, but, of
course, including the types of the involved variables. */

  macro if E:Exp then S:Stmt = if E then S else {}
  macro (for X = E1 to E2 do S) = {var X:int=E1; while X <= E2 do {S X=X+1;}}
  macro var E1:Exp, E2:Exp, Es:Exps; = var E1; var E2, Es;
  macro var X:#Id : T:Type = E; = var X : T; X = E;
end module


module SIMPLE-TYPED-STATIC
  imports SIMPLE-TYPED-STATIC-SYNTAX

/*@ \section{Type System}
Here we give the type system of SIMPLE using \K.  Like concrete
semantics, type systems defined in \K are also executable.  However,
\K type systems turn into type checkers instead of interpreters when
executed.

The typing process is done in two (overlapping) phases.  In the first
phase the global environment is built, which contains type bindings
for all the globally declared variables and functions.  For functions,
the declared types will be ``trusted'' during the first phase and
simply bound to their corresponding function names and placed in the
global type environment.  At the same time, type-checking tasks that
the function bodies indeed respect their claimed types are generated.
All these tasks are (concurrently) verified during the second phase.
This way, all the global variable and function declarations are
available in the global type environment and can be used in order to
type-check each function code.  This is consistent with the semantics
of untyped SIMPLE, where functions can access all the global variables
and can call any other function declared in the same program.  The
two phases may overlap because of the \K concurrent semantics.  For
example, a function task can be started while the first phase is still
running; moreover, it may even complete before the first phase does,
namely when all the global variables and functions that it needs have
already been processed and made available in the global environment by
the first phase task. */

/*@ \subsection{Extended syntax and results}
The idea is to start with a configuration holding the program to type
in one of its cells, then apply rewrite rules on it mixing types and
language syntax, and eventually obtain a type instead of the original
program.  In other words, the program ``evaluates'' to its type using
the \K rules giving the type system of the language.  In doing so,
additional typing tasks for function bodies are generated and solved
the same way.  If this rewriting process gets stuck, then we say that
the program is not well-typed.  Otherwise the program is well-typed
(by definition).

We start by allowing types to be used inside expressions and
statements in our language.  This way, types can be used together with
language syntax in subsequent \K rules without any parsing errors.
Also, since programs and fragments of program will ``evaluate'' to
their types, in order for the strictness and context declarations to
be executable we state that types are results. */

  syntax Exp ::= Type
  syntax Stmt ::= Type
  syntax KResult ::= Type

/*@ \subsection{Configuration}
The configuration of our type system consists of a \textsf{tasks} cell
holding various typing \textsf{task} cells, a global type environment,
and an \textsf{out} cell connected to the standard output to deliver
messages to the user.  Each task includes a \textsf{k} cell holding
the code to type, a \textsf{tenv} cell holding the local type
environment, and a \textsf{return} cell holding the return type of the
currently checked function.  The latter is needed in order to check
whether return statements return values of the expected type. 
Initially, the program is placed in a \textsf{k} cell inside a
\textsf{task} cell.  Since the cells with multiplicity ``?'' are not
included in the initial configuration, the \textsf{task} cell holding
the original program in its \textsf{k} cell will contain no other
subcells. */

  configuration <T color="red">
                  <tasks color="orange">
                    <task multiplicity="*" color="yellow">
                      <k color="green"> $PGM:Stmts </k>
                      <tenv multiplicity="?" color="cyan"> .Map </tenv>
                      <return multiplicity="?"> .K </return>
                    </task>
                  </tasks>
                  <gtenv color="blue"> .Map </gtenv>
                  <out stream="stdout"> .List </out>
                </T>

/*@ \subsection{Variable declarations}
Variable declarations type as statements, that is, they ``evaluate''
to the type \texttt{stmt}.  We did not need the \texttt{stmt} type as
part of the typed SIMPLE syntax (indeed, programmers are not allowed
to use the \texttt{stmt} type explicitly), so we define it now.  There
are three cases that need to be considered: when the list of variables
is empty (which happens when functions have no arguments, since we
reduce the typing of functions to typing variable declarations and
statements---see below), when a simple variable is declared, and when
an array variable is declared.  The macros at the end of the syntax
module above take care of reducing other variable declarations,
including ones where the declared variables are initialized, to only
these three cases.  The first case is trivial.  The second case has
two subcases: when the variable declaration is global (i.e., the
\textsf{task} cell contains only the \textsf{k} cell), in which case
it is added to the global type environment checking at the same time
that the variable has not been already declared (and outputting an
error message otherwise); and when the variable declaration is local
(i.e., a \textsf{tenv} cell is evaliable), in which case it is simply
added to the local type environment, possibly shadowing previous
homonymous variables.  The third case reduces to the second, but after
checking that the depth of the declared dimension type is smaller than
or equal to the depth of the declared type (it can be strictly
smaller, e.g., when we want the declared array to hold array
references). */

  syntax Type ::= "stmt"

  rule var .Types; => stmt   [:structural:]

  rule <task> <k> var X : T; => stmt ...</k> </task>
       <gtenv> Rho:Map (. => X|->T) </gtenv>
    if notBool(X in keys(Rho))

  rule <task> <k> var X : T;
               => error("Global identifier \"" + Id2String(X)
                        + "\" declared twice!\n") ...</k> </task>
       <gtenv>...X|->_...</gtenv>

  rule <k> var X:#Id : T:Type; => stmt ...</k>
       <tenv> Rho:Map => Rho[T / X] </tenv>

  context var _[[HOLE]] : _;
  rule var X[Ts:Types] : T; => checkDepth(Ts,T) ~> var X : T;  [:structural:]
  syntax K ::= "checkDepth" "(" Types "," Type ")"
  rule checkDepth((int,Ts => Ts), (arrayOf T => T))   [:structural:]
  rule checkDepth(.Types,_) => .K                     [:structural:]


/*@ \subsection{Function declarations}
Functions are allowed to be declared only at the top level (the
\textsf{task} cell holds only its \textsf{k} subcell).  Each function
declaration reduces to a variable declaration (a binding of its name
to its declared function type), but also adds a task into the
\textsf{tasks} cell.  The task consists of a typing of the statement
declaring all the function parameters followed by the function body,
together with the expected return type of the function.  The
\texttt{types} operation ensures that all the ``expressions'' in $\it
XTs$ are actually nothing but typed identifiers. */

  rule <task> <k> function F:#Id(XTs:Exps) : T S:Stmt
               => var F : function from types(XTs) to T; ...</k> </task>
       (. => <task>
               <k> var XTs; S </k>
               <tenv> . </tenv>
               <return> T </return>
             </task>)                                  [:structural:]
  syntax Types ::= "types" "(" Exps ")"                [:prec(1):]
  rule types(.Exps) => void,.Types                     [:structural:]
  rule types(X : T) => T,.Types                        [:structural:]
  rule types(X : T, E:Exp, Es:Exps) => T, types(E,Es)  [:structural:]

/*@ Once the entire program is processed, generating appropriate tasks
to type check its function bodies, we can dissolve the main
\textsf{task} cell (the one holding only a \textsf{k} subcell).  Since
we want to enforce that programs include a main function, we also
perform a check for \textsf{main} in the global type environment
(remove this check if you do not want your type system to reject
programs without a \texttt{main} function). */

  rule (<task> <k> stmt </k> </task> => .)
       <gtenv>...main |-> function from void to void...</gtenv>  [:structural:]

  rule <task> <k> stmt => error("No main():void function!\n") </k> </task>
       <gtenv> Rho </gtenv>
    if notBool(Rho(main) ==Bool function from void to void)
    [:structural:]

/*@ Similarly, once a non-main task (i.e., one which also contains
\textsf{tenv} and \textsf{return} subcells) is completed using the
subsequent rules (i.e., its \textsf{k} cell holds only the type
\texttt{stmt}), we can dissolve its corresponding cell.  In the end,
there should be no task cell left in the configuration when the
program correctly type checks, so we can also issue a corresponding
success message. */

  rule <task> <k>stmt</k> Rest:Bag </task> => .
    if notBool(Rest ==Bool .)  [:structural:]
  rule (<tasks> .Bag </tasks> => .)
       <out>... . => ListItem("Type checked!\n") </out>
    [:structural:]

/*@ \subsection{Expressions}
In theory, the first three rewrite rules below can apply anywhere
to rewrite values into their types, not only at the top of the
\textsf{k} cell.  Unfortunately, since the \K tool is implemented also
by rewriting, that would get into conflict with the internals of our
implementation, so we restrict their application to the top of the
\textsf{k} cell. */

  rule <k> I:#Int => int ...</k>
  rule <k> B:#Bool => bool ...</k>
  rule <k> Str:#String => string ...</k>

/*@ The are two cases to distinguish for variable lookup: if the
variable is bound in the local type environment, then look its type up
there; otherwise, look its type up in the global environment. */

  rule <k> X => T ...</k> <tenv>... X |-> T ...</tenv>
  rule <k> X => T ...</k> <tenv> Rho </tenv> <gtenv>... X |-> T ...</gtenv> 
    if notBool(X in keys(Rho))

  rule <k> X => error("Identifier \"" + Id2String(X) + "\" not declared!")
       ...</k>
       <tenv> Rho </tenv> <gtenv> Rho':Map </gtenv>
    if notBool(X in keys(Rho) keys(Rho'))

/*@ We want the increment operation to apply to any lvalue, including
array elements, not only to variables.  For that reason, we define a
special context extracting the type of the argument of the increment
operation only if that argument is an lvalue.  Otherwise the rewriting
process gets stuck.  The type of the lvalue is expected to be an
integer in order to be allowed to be incremented, as seen in the rule
``\texttt{++ int => int}'' below. */

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
  rule _`(_`)(function from Ts to T, Ts) => T
    if Ts =/=Bool .Types
  rule _`(_`)(function from void to T, .Types) => T
  rule read() => int

/*@ The special context and the rule for assignment below are similar
to those for increment: the LHS of the assignment must be an lvalue
and, in that case, it must have the same type as the RHS, which then
becomes the type of the assignment. */

  context ([HOLE] => ltype([HOLE])) = _
  rule T=T => T


/*@ \subsection{Statements}
To avoid having to recover type environments after blocks, we prefer
to start a new task for block body, making sure that the new task
is passed the same type environment and retun cells.  The value
returned by \texttt{return} statements must have the same type as
stated in the \textsf{return} cell.  The \texttt{print} variadic
function is allowed to only print integers and strings.  The thrown
exceptions can only have integer type. */

  rule {} => stmt
  rule <task> <k> {Ss:Stmts} => stmt ...</k> Rest </task>
       (. => <task> <k> Ss </k> Rest </task>)
    if notBool(Rest ==Bool .)
  rule T; => stmt
  rule if bool then stmt else stmt => stmt
  rule while bool do stmt  => stmt
  rule <k> return T; => stmt ...</k> <return> T </return>
  rule return; => stmt
  rule print(T,Ts => Ts);  if T ==Bool int orBool T ==Bool string
  rule print(.Types); => stmt
  rule try stmt catch(X) S => {var X:int; S}
    [:structural:]
  rule throw int; => stmt
  rule spawn stmt => stmt
  rule acquire T; => stmt
  rule release T; => stmt
  rule rendezvous_;(T) => stmt

  rule stmt stmt => stmt

//@ Error reporting
  syntax K ::= "error" "(" Exp ")" [:strict:]
             | "stuck"
  rule <k> error(Str) => stuck ...</k>
       <out>... . => ListItem(Str) </out>

end module
