
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
                | "arrayOf" Type [:prec(1):]
                | "function" "from" Types "to" Type
                    [:prec(1) latex "{#1}\rightarrow{#2}":]
  syntax Types ::= List{Type,","}

/*@ \subsection{Declarations}
Variable and function declarations are allowed to have a more generous
syntax than how we want them to be used in programs, but the type system
will be defined in such a way that all abuses will be caught.  For example,
functions will only be allowed to take typed identifiers as parameters.
The reason we prefer to allow a more generous syntax is to simplify our
overall syntax by defining fewer syntactic categories.  Recall that, after
all, the syntax one defined in \K definition is what we call "the syntax
of the semantics", that is, some syntax which is convenient enough for users
to write their desired semantic rules.  This syntax is not meant to be used
to parse complex programming language, such as C or Java.  While \K's syntax
is good enough to parse simple and pedagogical languages like the ones
discussed in this class, in practice one is expected to use external parsers
for complex languages. */

  syntax Decl ::= "var" Exps ";"
                | "function" #Id "(" Exps ")" ":" Type Stmt

/*@ \subsection{Expressions}
The syntax of expressions is identical to that in untyped SIMPLE, except
for the last construct in the sequence below.  That is allowed exclusively only
for parsing declarations as described above.  It will be given no semantics. */

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
The statements have the same syntax as in untyped SIMPLE.  That is because
we decided that counters in \texttt{for} loops and values as exceptions
can only be integers, so there is no need to declare them so (we will assume
that in the semantics of these language constructs).  Note that, unlike in
untyped SIMPLE, all statement constructs which have arguments and are not
desugared are strict, including the conditional and the \texttt{while}.
Indeed, from a typing perspective, they are all strict: first type their
arguments and then type the actual construct. */

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

/*@ We use the same desugaring macros like in untyped SIMPLE, but, of course,
including the types of the involved variables. */

  macro if E:Exp then S:Stmt = if E then S else {}
  macro (for X = E1 to E2 do S) = {var X:int=E1; while X <= E2 do {S X=X+1;}}
  macro var E1:Exp, E2:Exp, Es:Exps; = var E1; var E2, Es;
  macro var X:#Id : T:Type = E; = var X : T; X = E;
end module


module SIMPLE-TYPED-STATIC
  imports SIMPLE-TYPED-STATIC-SYNTAX

/*@ \section{Type System}
Here we give the type system of SIMPLE using \K.  Like concrete semantics,
type systems defined in \K are also executable.  However, \K type systems
turn into type checkers instead of interpreters when executed.

The typing process is done in two (overlapping) phases.  In the first phase
the global environment is built, which contains type bindings for all the
globally declared variables and functions.  For functions, the declared types
will be ``trusted'' during the first phase and simply bound to their
corresponding function names and placed in the global type environment.
At the same time, type-checking tasks that the function bodies indeed respect
their claimed types are generated.  All these tasks are (concurrently) verified
during the second phase.  This way, all the global variable and function
declarations are available in the global type environment and can be used in
order to type-check each function code.  This is consistent with the semantics
of untyped SIMPLE, where functions can access all the global variables and can
call any other functions declared in the same program.  The two phases may
overlap because of the \K concurrent semantics.  For example, a function task
can be started while the first phase is still running; moreover, it may even
complete before the first phase does, namely when all the global variables and
functions that it needs have already been processed and made available in the
global environment by the first phase task. */

/*@ \subsection{Extended syntax and results}
The idea is to start with a configuration holding the program to type in
one of its cells, then apply rewrite rules on it mixing types and language
syntax, and eventually obtain a type instead of the original program.  In other
words, the program ``evaluates'' to its type using the \K rules giving the
type system of the language.  In doing so, additional typing tasks for function
bodies are generated and solved the same way.  If this rewriting process gets
stuck, then we say that the program is not well-typed.  Otherwise the program
is well-typed (by definition).

We start by allowing types to be used inside expressions and statements in
our language.  This way, types can be used together with language syntax in
subsequent \K rules without any parsing errors.  Also, since programs and
fragments of program will ``evaluate'' to their types, in order for the
strictness and context declarations to be executable we state that types are
results. */

  syntax Exp ::= Type
  syntax Stmt ::= Type
  syntax KResult ::= Type

/*@ \subsection{Configuration}
The configuration of our type system consists of \textsf{task} cells and
a global type environment.  Each task includes a \textsf{k} cell holding
the code to type and two optional cells:
\begin{itemize}
\item A \textsf{tenv} cell holding the local type environment.
\item A \textsf{return} cell holding the return type of the currently 
checked function.  This is needed in order to check whether return statements
return values of the expected type.
\end{itemize}
The original program is put in a task containing no return or type environment
cells (not that the multiplicity of these cells is ``?'', which means that they
are not automatically included in the initial configuration. */

  configuration <T color="red">
                  <task multiplicity="*" color="yellow">
                    <k color="green"> $PGM:Stmts </k>
                    <tenv multiplicity="?" color="cyan"> .Map </tenv>
                    <return multiplicity="?"> .K </return>
                  </task>
                  <gtenv color="blue"> .Map </gtenv>
                </T>

/*@ \subsection{Variable declarations}
Variable declarations type as statements, that is, they ``evaluate'' to
the type \texttt{stmt}.  We did not need the \texttt{stmt} type as part of the
typed SIMPLE syntax (indeed, users are not allowed to use the statement type
explicitly), so we define it now.  There are three cases that need to be
considered: when the list of variables is empty (which can appear
when functions have no arguments, since we reduce the typing of functions
to typing variable declarations and statements---see below), when a simple
variable is declared, and when an array variable is declared.  The macros
at the end of the syntax module above take care of reducing other variable
declarations, including ones where the declared variables are initialized,
to only these three cases.  The first case is trivial and the second and third
make use of a \texttt{bindto} helper operation, which takes a variable and a
type and performs the actual binding in the current type environment cell when
it reaches the top of the computation.  Note that \texttt{bindto} applies the
binding to the local type environment when that exists; otherwise it applies it
to the global type environment.  The third case requires an additional
check, namely that the depth of the declared dimension type is smaller than or
equal to the depth of the declared type (it can be strictly smaller, e.g.,
when we want the declared array to hold array references).
The auxiliary operations (e.g., \texttt{checkDepth} and
\texttt{bindto}) are defined at the end of the module, as usual. */

  syntax Type ::= "stmt"

  rule var; => stmt   [: structural:]
  rule var X:#Id : T:Type; => bindto(X,T)
  context var _[[HOLE]] : _;
  rule var X[Ts:Types] : T; => checkDepth(Ts,T) ~> bindto(X,T)

/*@ \subsection{Function declarations}
Functions are allowed to be declared only at the top level, indicated in
the rule below by the fact that the \textsf{task} cell holds only a
\textsf{k} cell.  Indeed, as the rule below shows, generated function body
tasks also contain \textsf{tenv} and \textsf{return} cells.
Each function declaration adds a binding of its name to its declared
function type in the current (in this case the global) type environment,
but also adds a task into the \textsf{tasks} cell.  The task consists of
a typing a the statement declaring all the function parameters followed
by the function body, together with the expected return type of the function.
The code of the task makes use of other language constructs (variable
declaration and sequential composition), so it is not very modular,
but it is more compact and easier to understand than a more direct
semantics.  The auxiliary \texttt{types} operation, defined at the
end of this module, will ensure that all the ``expressions'' in
$\it XTs$ are actually nothing but typed identifiers.  */

  rule <task>
         <k> function F:#Id(XTs:Exps) : T S:Stmt =>
             bindto (F, function from types(XTs) to T) ...</k>
       </task>
       (. => <task>
               <k> var XTs; S </k>
               <tenv> . </tenv>
               <return> T </return>
             </task>)

/*@ Once a task is completed, indicated by the fact that its
\textsf{k} cell holds only the type \texttt{stmt}, we can dissolve its
corresponding cell.  Since the task may be the original one and since
we want to enforce that programs include a main function, we also
perform a check for \textsf{main} in the global type environment.
This way, there should be no task cell left in the configuration when
the program correctly type checks. */

  rule (<task>... <k> stmt </k> ...</task> => .)
       <gtenv>... main |-> function from _ to _ ...</gtenv>

/*@ \subsection{Expressions}
Now that the entire machinery of the type system is operational, it is
straightforward to type the various language constructs. */

/*@ In theory, the first three rewrite rules below can apply anywhere
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
  rule <k> X => T ...</k> <gtenv>... X |-> T ...</gtenv> <tenv> Rho </tenv>
    if notBool(X in keys(Rho))

/*@ We want the increment operation to apply to any lvalue, including
array elements, not only to variables.  For that reason, we define the
following special context which extracts the type of the argument of
the increment operation only if that argument is an lvalue.
Otherwise the rewriting process gets stuck.  See the definition of
\texttt{ltype} at the end of this module.  The type of the lvalue is
expected to be an integer in order to be allowed to be incremented, as
seen in the rule ``\texttt{++ int => int}'' below. */

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
  rule T[] => T
  rule sizeOf(arrayOf T) => int
  rule _`(_`)(function from Ts to T, Ts) => T
  rule read() => int

/*@ The special context and the rule for assignment below are similar
to those for the increment operation above: the LHS of the assignment
must be an lvalue and, in that case, it must have the same
type as the RHS, which thus becomes the type of the assignment. */

  context ([HOLE] => ltype([HOLE])) = _
  rule T=T => T


/*@ \subsection{Statements}
Statements are also straightforward to be given a typing policy now.
Note that the type environment is recovered after each block (see the
definition of \texttt{tenv} at the end of this module), that the value
returned by \texttt{return} statements must have the same type as
stated in the \textsf{return} cell, that the \texttt{print} variadic
function is allowed to only print integers and strings, and that thrown
exceptions can only have integer type. */

  rule {} => stmt
  rule <k> {Ss:Stmts} => Ss ~> tenv(Rho) ...</k> <tenv> Rho </tenv>
  rule T; => stmt
  rule if bool then stmt else stmt => stmt
  rule while bool do stmt  => stmt
  rule <k> return T; => stmt ...</k> <return> T </return>
  rule return; => stmt
  rule print(int,Ts => Ts);
  rule print(string,Ts => Ts);
  rule print(); => stmt
  rule try stmt catch(X) S => {var X:int; S}   [:structural:]
  rule throw int; => stmt
  rule spawn stmt => stmt
  rule acquire T; => stmt
  rule release T; => stmt
  rule rendezvous_;(T) => stmt

  rule stmt stmt => stmt

//@ \subsection{Auxiliary operations}

/*@ The \texttt{ltype} operation below evaluates to the type of its
argument, but only if that argument is an lvalue, that is, a variable
or an array element. */
  syntax Exp ::= "ltype" "(" Exp ")"
  rule ltype(X) => X        [:structural:]
  rule ltype(E:Exp[Es:Exps]) => E[Es]        [:structural:]

/*@ The two operations below are standard, we use them in many \K
definitions.  Note, however, that \texttt{bindto} evaluates to
\texttt{stmt} and, moreover, that it fist attempts to do the binding
locally; if a local environment is not available, meaning that one
attempts to bind a top-level variable or function name, then does the
binding in the global type environment. */

  syntax K ::= "bindto" "(" #Id "," Type ")"
             | "tenv" "(" Map ")"
  rule <k> bindto(X,T) => stmt ...</k>
       <tenv> Rho:Map => Rho[T / X] </tenv>           [:structural:]
  rule <task> <k> bindto(X,T) => stmt ...</k> </task>
       <gtenv> Rho:Map => Rho[T / X] </gtenv>         [:structural:]

  rule <k> stmt ~> (tenv(Rho) => .) ... </k>
       <tenv> _ => Rho </tenv>                        [:structural:]

/*@ The operation below makes sure that the list of types passed as
its first argument are all integers and there is sufficient
``\texttt{arrayOf}'' depth in the second argument type to justify
them.  Recall from above that this operation is used to check
whether a particular array declaration type-checks. */

  syntax K ::= "checkDepth" "(" Types "," Type ")"
  rule checkDepth((int,Ts => Ts), (arrayOf T => T))   [:structural:]
  rule checkDepth(.Types,_) => .K                     [:structural:]

/*@ Finally, the operation below ensures that its argument is a list
of typed identifiers (as needed for the parameters in function
declarations) and it rewrites to the list of their types. */

  syntax Types ::= "types" "(" Exps ")"    [:prec(1):]
  rule types() => .Types                   [:structural:]
  rule types(X : T, XTs) => T, types(XTs)  [:structural:]

end module
