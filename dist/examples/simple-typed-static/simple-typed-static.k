
module SIMPLE-TYPED-STATIC-SYNTAX

/*@ \section{Syntax}
The syntax of typed SIMPLE extends that of untyped SIMPLE with support
for declaring types to variables and functions. */

/*@ \subsection{Types}
Primitive, array and function types, as well as lists (or tuples) of types.
The lists of types are useful for function arguments. */

  syntax Type ::= "void" | "int" | "bool" | "string"
                | Type "[" "]"
                > Types "->" Type
                | "(" Type ")"             [bracket]

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

  syntax Param ::= Type Id
  syntax Params ::= List{Param,","}

  syntax Decl ::= Type Exps ";"
                | Type Id "(" Params ")" Block

/*@ \subsection{Expressions}
The syntax of expressions is identical to that in untyped SIMPLE,
except for the last construct in the sequence below.  That is allowed
exclusively only for parsing declarations, as described above.  It
will be given no semantics. */

  syntax Exp ::= Int | Bool | String | Id
               | "(" Exp ")"             [bracket]
               | "++" Exp
               > Exp "[" Exps "]"        [strict]
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
                 Exp "&&" Exp            [strict, left]
               | Exp "||" Exp            [strict, left]
               > "spawn" Block
               > Exp "=" Exp             [strict(2), right]

  syntax Exps ::= List{Exp,","}          [strict, hybrid]


/*@ \subsection{Statements}
The statements have the same syntax as in untyped SIMPLE.  That is
because we decided that counters in \texttt{for} loops and thrown
exceptions can only be integers, so there is no need to declare them.
Note that, unlike in untyped SIMPLE, all statement constructs which
have arguments and are not desugared are strict, including the
conditional and the \texttt{while}.  Indeed, from a typing
perspective, they are all strict: first type their arguments and then
type the actual construct. */

  syntax Block ::= "{" "}"
                | "{" Stmts "}"

  syntax Stmt ::= Decl | Block
                | Exp ";"                                  [strict]
                | "if" "(" Exp ")" Block "else" Block      [avoid, strict]
                | "if" "(" Exp ")" Block
                | "while" "(" Exp ")" Block                [strict]
                | "for" "(" Stmt Exp ";" Exp ")" Block
                | "return" Exp ";"                         [strict]
                | "return" ";"
                | "print" "(" Exps ")" ";"                 [strict]
                | "try" Block "catch" "(" Param ")" Block  [strict(1)]
                | "throw" Exp ";"                          [strict]
                | "join" Exp ";"                           [strict]
                | "acquire" Exp ";"                        [strict]
                | "release" Exp ";"                        [strict]
                | "rendezvous" Exp ";"                     [strict]

  syntax Stmts ::= Stmt
                |  Stmts Stmts                             [seqstrict, right]

/*@ We use the same desugaring macros like in untyped SIMPLE, but, of
course, including the types of the involved variables. */

  rule if (E) S => if (E) S else {}                                 [macro]
  rule for(Start Cond; Step) {S} => {Start while (Cond) {S Step;}}  [macro]
  rule T:Type E1:Exp, E2:Exp, Es:Exps; => T E1; T E2, Es;           [macro]
  rule T:Type X:Id = E; => T X; X = E;                              [macro]

  syntax Id ::= "main"
endmodule


module SIMPLE-TYPED-STATIC
  imports SIMPLE-TYPED-STATIC-SYNTAX

/*@ \section{Static semantics}
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

  syntax BlockOrStmtType ::= "block" | "stmt"
  syntax Type ::= BlockOrStmtType
  syntax Exp ::= Type
// I had to comment the sort inclusion below out, because the current
// parser parses declarations "T X;" as statement composition "T" "X;"
//  syntax Block ::= Type
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

  configuration <T color="yello">
                  <tasks color="orange">
                    <task multiplicity="*" color="yellow">
                      <k color="green"> $PGM:Stmts </k>
                      <tenv multiplicity="?" color="cyan"> .Map </tenv>
                      <return multiplicity="?" color="black"> void </return>
                    </task>
                  </tasks>
                  <br/>
                  <gtenv color="blue"> .Map </gtenv>
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

  rule <task> <k> T:Type X:Id; => stmt ...</k> </task>
       <gtenv> Rho (. => X |-> T) </gtenv>
    when notBool(X in keys(Rho))

// so we allow the same variables declared multiple times locally
  rule <k> T:Type X:Id; => stmt ...</k> <tenv> Rho => Rho[T/X] </tenv>

  context _:Type _[HOLE];

// E can be X[7,8][3,4], etc.
// I don't understand why the rule below works well, that is, why its LHS
// completed into T E[int,Ts],.Exps; (and similarly for the RHS)
  rule T:Type E[int,Ts:Types]; => T[] E[Ts];  [structural]
// I want to write the rule below as _:Type (E:Exp[.Types] => E);
  rule T:Type E:Exp[.Types]; => T E;          [structural]

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

  rule <task> <k> T:Type F:Id(Ps:Params) S => types(Ps)->T F; ...</k> </task>
       (. => <task>
               <k> mkDecl(Ps) S </k> <tenv> . </tenv> <return> T </return>
             </task>)
    [structural]

  syntax Decl ::= mkDecl(Params)
  rule mkDecl(T:Type X:Id, Ps:Params) => T X; mkDecl(Ps)
  rule mkDecl(.Params) => stmt

/*@ Once the entire program is processed (generating appropriate tasks
to type check its function bodies), we can dissolve the main
\textsf{task} cell (the one holding only a \textsf{k} subcell).  Since
we want to enforce that programs include a main function, we also
generate a function task executing \texttt{main()} to ensure that it
types (remove this task creation if you do not want your type system
to reject programs without a \texttt{main} function). */

// note that a return cell not needed to be added
// we move the global type environment atomically in gtenv
  rule <task> <k> stmt => main(.Exps); </k> (. => <tenv> . </tenv>) </task>
    [structural]

/*@ Similarly, once a non-main task (i.e., one which also contains
\textsf{tenv} and \textsf{return} subcells) is completed using the
subsequent rules (i.e., its \textsf{k} cell holds only the type
\texttt{stmt}), we can dissolve its corresponding cell.  In the end,
there should be no task cell left in the configuration when the
program correctly type checks, so we can also issue a corresponding
success message. */

// tenv needed only to ensure this is not the global task
// T can also be a block (e.g., when having nested blocks {{S}}
  rule <task>... <k> _:BlockOrStmtType </k> <tenv> _ </tenv> ...</task> => .

/*@ \subsection{Expressions}
In theory, the first three rewrite rules below can apply anywhere
to rewrite values into their types, not only at the top of the
\textsf{k} cell.  Unfortunately, since the \K tool is implemented also
by rewriting, that would get into conflict with the internals of our
implementation, so we restrict their application to the top of the
\textsf{k} cell. */

  rule _:Int => int
  rule _:Bool => bool
  rule _:String => string

/*@ The are two cases to distinguish for variable lookup: if the
variable is bound in the local type environment, then look its type up
there; otherwise, look its type up in the global environment. */

  rule <k> X:Id => T ...</k> <tenv>... X |-> T ...</tenv>

  rule <k> X:Id => T ...</k> <tenv> Rho </tenv> <gtenv>... X |-> T ...</gtenv> 
    when notBool(X in keys(Rho))

  rule <task> <k> X:Id => T ...</k> </task> <gtenv>... X |-> T ...</gtenv> 

/*@ We want the increment operation to apply to any lvalue, including
array elements, not only to variables.  For that reason, we define a
special context extracting the type of the argument of the increment
operation only if that argument is an lvalue.  Otherwise the rewriting
process gets stuck.  The type of the lvalue is expected to be an
integer in order to be allowed to be incremented, as seen in the rule
``\texttt{++ int => int}'' below. */

// move to auxilliary
  syntax Exp ::= ltype(Exp)
  rule ltype(X:Id) => X                   [structural]
  rule ltype(E:Exp [Es:Exps]) => E[Es]    [structural]

  context ++(HOLE => ltype(HOLE))
  rule ++ int => int
  rule int + int => int
  rule string + string => string
  rule int - int => int
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
  rule bool && bool => bool
  rule bool || bool => bool
  rule ! bool => bool

// need parentheses in the RHS for now, to avoid caturing Ts as rule tag
  rule (T[])[int, Ts:Types] => (T[Ts])
  rule T[.Types] => T

  rule sizeOf(T[]) => int

  rule (Ts:Types -> T)(Ts) => T when Ts =/=K .Types
  rule (void -> T)(.Types) => T

  rule <k> return T:Type; => stmt ...</k> <return> T </return>
  rule <k> return; => stmt ...</k> <return> _ </return>

  rule read() => int

/*@ The special context and the rule for assignment below are similar
to those for increment: the LHS of the assignment must be an lvalue
and, in that case, it must have the same type as the RHS, which then
becomes the type of the assignment. */

  context (HOLE => ltype(HOLE)) = _
  rule T:Type = T => T


/*@ \subsection{Statements}
To avoid having to recover type environments after blocks, we prefer
to start a new task for block body, making sure that the new task
is passed the same type environment and retun cells.  The value
returned by \texttt{return} statements must have the same type as
stated in the \textsf{return} cell.  The \texttt{print} variadic
function is allowed to only print integers and strings.  The thrown
exceptions can only have integer type. */

  rule {} => block

  rule <task> <k> {S} => block ...</k> <tenv> Rho </tenv> R </task>
       (. => <task> <k> S </k> <tenv> Rho </tenv> R </task>)

  rule T:Type; => stmt
// nasty parentheses needed around first block; why not the second, too?
// well, the second is needed too, otherwise same error as below
  rule if (bool) (block) else (block) => stmt
// didn't need parantheses around block; why?
// well, we needed them
  rule while (bool) (block) => stmt
  rule print(T:Type, Ts => Ts); when T ==K int orBool T ==K string
  rule print(.Types); => stmt
// had to put parenteses around block, to trick the parser it is K
  rule try (block) catch(int X:Id) {S} => {int X; S}  [structural]
  rule throw int; => stmt
// no return cell in the spawned thread on purpose (not allowed to return)
  rule <k> spawn S => int ...</k> <tenv> Rho </tenv>
       (. => <task> <k> S </k> <tenv> Rho </tenv> </task>)
  rule join int; => stmt
  rule acquire T:Type; => stmt
  rule release T:Type; => stmt
  rule rendezvous T:Type; => stmt

  rule _:BlockOrStmtType _:BlockOrStmtType => stmt

/*@ An auxiliary \texttt{stuck} construct, displayed as a frame in
the generated PDF, used to stuck computations with whatever
computation we want as argument.  This should be generic, part of the
\K framework. */

  syntax K ::= stuck(K)  [latex(\framebox{${#1}$})]

  syntax Types ::= types(Params)  [function]
  rule types(T:Type _:Id) => T, .Types
  rule types(T:Type _:Id, P, Ps) => T, types(P,Ps)
  rule types(.Params) => void, .Types

endmodule
