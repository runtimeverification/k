require "modules/pattern-matching.k"

/*!
\title{FUN --- Untyped}
\author{Grigore Ro\c{s}u and Traian Florin \c{S}erb\u{a}nu\c{t}\u{a}
        (\texttt{\{grosu,tserban2\}@illinois.edu})}
\organization{University of Illinois at Urbana-Champaign}
*/

/*@ \section{Abstract}

This is the \K semantic definition of the untyped FUN language.
FUN is a pedagogical and research language that captures
the essence of the functional programming paradigm, extended with several
features often encountered in functional programming languages.
Like many functional languages, FUN is an expression language,
that is, everything, including the main program, is an expression.
Functions can be declared anywhere and are first class values in the
language.  FUN is call-by-value here, but it has been extended (as
student homework assignments) with other parameter-passing styles.
To make it more interesting and to highlight some of \K's strengths,
FUN includes the following features in addition to the conventional
functional constructs encountered in similar languages used as
teaching material:
\begin{itemize}
\item Integers and Booleans, plus two builtin data-types, namely
tuples and lists, which can be used arbitrarily nested.
Tuples use the syntax \texttt{\{1,2,3\}} and lists the syntax
\texttt{[1,2,3]}.
\item Functions and \texttt{let}/\texttt{letrec} binders can take
multiple space-separated arguments, but these are desugared to
ones that only take one argument, by currying.  For example, the
expressions
\begin{verbatim}
fun x y -> x y
let x y = y in x
\end{verbatim}
are desugared, respectively, into the following expressions:
\begin{verbatim}
fun x -> fun y -> x y
let x = fun y -> y in x
\end{verbatim}
\item Functions can be defined using pattern matching over the
available data-types.  For example, the program
\begin{verbatim}
letrec max = fun [h] -> h
             |   [h|t] -> let x = max t
                          in  if h > x then h else x
in max [1, 3, 5, 2, 4, 0, -1, -5]
\end{verbatim}
defines a function \texttt{max} that calculates the maximum element of
a non-empty list, and the function
\begin{verbatim}
letrec ack = fun {0,n} -> n + 1
             |   {m,0} -> ack {m - 1, 1}
             |   {m,n} -> ack {m - 1, ack {m, n - 1}}
in ack {2,3}
\end{verbatim}
calculates the Ackermann function applied to a particular pair of
numbers.  Patterns can be nested.  Patterns can currently only be used
in function definitions, and not directly in
\texttt{let}/\texttt{letrec} binders.  For example, this is not
allowed:
\begin{verbatim}
let {x,y} = {1,2} in x+y
\end{verbatim}
But this is allowed:
\begin{verbatim}
let f{x,y} = x+y in f{1,2}
\end{verbatim}
because it is first reduced to
\begin{verbatim}
let f = fun {x,y} -> x+y in f{1,2}
\end{verbatim}
by uncurrying of the \texttt{let} binder, and pattern matching is
allowed in function arguments.
\item We include a \texttt{callcc} construct, for two reasons: first,
several functional languages support this construct; second, some
semantic frameworks have a hard time defining it.  Not \K.
\item Finally, we include mutables by means of referencing an
expression, getting the reference of a variable, dereferencing and
assignment.  We include these for the same reasons as above: there
are languages which have them, and they are not easy to define in some
semantic frameworks.
\end{itemize}
Like in many other languages, some of FUN's constructs can be
desugared into a smaller set of basic constructs.  We do that as
usual, at the end of the syntax module using macros, and then we only
give semantics to the core constructs.

\paragraph{Note:}{
We recommend the reader to first consult the dynamic semantics (at
least the environment-based definition) of the LAMBDA++ language in
the K Tutorial.  To keep the comments below small and focused, we will
not re-explain functional or \K features that have already been
explained in the tutorial.}  */

module FUN-UNTYPED-SYNTAX

/*@ \section{Syntax}

FUN is an expression language.  The constructs below fall into
several categories: arithmetic constructs, conventional functional
constructs, pattern matching, lists, references, and
call-with-current-continuation (callcc).  The arithmetic constructs
are standard; they are present in almost all our \K language
definitions.  The meaning of FUN's constructs are discussed in more
depth when we define their semantics in the next module.  */

  syntax Exp ::= Int | Bool | Id
               | "(" Exp ")"             [bracket]
// Unary minus currently needs to be removed, to avoid parsing ambiguities
//               | "-" Exp                           [strict]
               | Exp Exp                           [strict, left]
               | "&" Id
               | "@" Exp                           [strict]
               | "callcc" Exp                      [strict]
               | "cons" Exp Exp                    [strict]
               > left:
                 Exp "*" Exp                       [strict, left]
               | Exp "/" Exp                       [strict, left]
               | Exp "%" Exp                       [strict, left]
               > left:
                 Exp "+" Exp                       [strict, left]
               | Exp "-" Exp                       [strict, left, prefer]
               > non-assoc:
                 Exp "<" Exp                       [strict, non-assoc]
               | Exp "<=" Exp                      [strict, non-assoc]
               | Exp ">" Exp                       [strict, non-assoc]
               | Exp ">=" Exp                      [strict, non-assoc]
               | Exp "==" Exp                      [strict, non-assoc]
               | Exp "!=" Exp                      [strict, non-assoc]
               > "!" Exp                           [strict]
               > left:
                 Exp "&&" Exp                      [strict(1), left]
               | Exp "||" Exp                      [strict(1), left]
               > Exp ":=" Exp                      [strict]
               > "let" Bindings "in" Exp
// The "prefer" attribute for letrec currently needed due to tool bug
               | "letrec" Bindings "in" Exp        [prefer]
               | "if" Exp "then" Exp "else" Exp    [strict(1)]
               | "try" Exp "catch" "(" Id ")" Exp
               > Exp ";" Exp                       [strict(1), right]
               > "fun" Cases
/*@ A function is essentially a ``\texttt{|}''-separated ordered
sequence of cases, each case of the form ``\verb|pattern -> expression|'',
preceded by the language construct \texttt{fun}. */
// I wish I were able to use just parentheses for tuples ...
// Unfortunately, that gets into parsing ambiguities with (...) for grouping
               | "{" Exps "}"          [strict]  // tuple
               | "[" Exps "]"          [strict]  // lists
               | "[" Exps "|" Exp "]"            // list [head|tail] pattern

/*@ FUN tuples and lists are formed by enclosing comma-separated
sequences of expressions (i.e., terms of sort \textit{Exps}) in curly
brackets and, respectively, in square brackets.  In function patterns,
we also allow patterns following the usual head/tail notation; for
example, the pattern $\tt [x_1,...,x_n|t]$ binds $\tt x_1$, ..., $\tt x_n$
to the first elements of the matched list, and $\tt t$ to the list
formed with the remaining elements. */

/*@ References are first class values in FUN.  The construct
\texttt{\&} evaluates to a reference, namely one where the
variable passed as argument stores its value.  The construct
\texttt{@} takes a reference and evaluates to the value stored there.
The construct \texttt{:=} takes two expressions, the first expected to
evaluate to a reference; the value of its second argument will be
stored at the location to which the first points (the old value is
thus lost).  Finally, since expression evaluation now has side
effects, it makes sense to also add a sequential composition
construct, which is sequentially strict.  This evaluates to the value
of its second argument; the value of the first argument is lost (which
has therefore been evaluated only for its side effects. */

//@ Syntactic lists used above:

  syntax Exps ::= List{Exp,","}        [strict]
  syntax Ids  ::= List{Id,","}

/*@ Recall that the syntax that we define in \K is not meant to
serve as a ultimate parser for the defined language, but rather as a
convenient notation for \K abstract syntax trees, which we prefer when
we write the semantic rules.  It is therefore often the case that we
define a more ``generous'' syntax than we want to allow programs to
use.  We do it here, too.  Specifically, the syntax of \textit{Cases}
and of \textit{Bindings} allows any expressions to appear as patterns
or as bindings.  This syntactic relaxation permits many wrong programs
to be parsed, but that is not a problem because we are not going to
give semantics to wrong combinations, so those programs will get
stuck; moreover, our type inferencer will reject those programs anyway. */

  syntax Case  ::= Exp "->" Exp
  syntax Cases ::= List{Case, "|"}

  syntax Binding  ::= Exp "=" Exp
  syntax Bindings ::= List{Binding,"and"}


//@ \subsection{Desugaring macros}

//@ Uncurrying of multiple arguments in functions and binders:

  rule P1 P2 -> E => P1 -> fun P2 -> E                       [macro]
  rule F P = E => F = fun P -> E                             [macro]

//@ Multiple-head list patterns desugar into successive one-head patterns:

  rule [E:Exp,Es|T] => [E|[Es|T]]  when Es =/=K .Exps        [macro]

/*@ The following identifiers have a special meaning, which is
easily defined by desugaring to other expressions, defined using
macros.  In order to do that we need some new variables; for those, we
follow the same convention like in the \K tutorial, where we added
them as new identifier constructs starting with the character $\$$, so
we can easily recognize them when we debug or trace the semantics. */

  syntax Id ::= "head" | "tail" | "null?" | "ref" | "throw"
  syntax Id ::= "$h" | "$t" | "$l" | "$x" | "$k" | "$v"
  rule head => fun [$h|$t] -> $h                             [macro]
  rule tail => fun [$h|$t] -> $t                             [macro]
  rule null? => fun [.Exps] -> true | [$h|$t] -> false       [macro]

/*@ We used the name \texttt{head} for the function that extracts the
first element of the list if the list has at least one element (and
gets stuck otherwise), \texttt{tail} evaluates to the rest of the list
except the first element and fails if the list is empty, and
\texttt{null?} checks whether the list is empty.  The semantics of
\texttt{cons}, which adds an element to the beginning of a list
(\texttt{cons} is the dual of \texttt{head} and \texttt{tail}) cannot
be defined the same way using macros; its explicit semantics is
defined later, in the semantics module.  */

/*@ The next rule defines \texttt{ref}, which takes one argument,
evaluates it, stores it at a fresh location, and finally returns that
location.  Its definition below does precisely all these: */

  rule ref => fun $x -> & $x                                 [macro]

/*@ The above works because \texttt{\&}, whose semantics is defined later in
the semantics module, takes a variable and returns its location
(like in C).  Note that some ``pure'' functional programming
researchers strongly dislike the \texttt{\&} construct, but favor
\texttt{ref}.  We refrain from having a personal opinion on this issue
here, but support \texttt{\&} in FUN because it is, technically speaking,
more powerful than \texttt{ref}.  From a language design perspective,
it would be equally easy to drop \texttt{\&} and instead give a direct
semantics to \texttt{ref}. */

/*@ Call-with-current-continuation, named \texttt{callcc} in FUN, is a
powerful control operator that originated in the Scheme programming
language, but it now exists in many other functional languages.  It
works by evaluating its argument, expected to evaluate to a function,
and passing the current continuation, or evaluation context (or
computation, in \K terminology), as a special value to it.  When/If
this special value is invoked, the current context is discarded and
replaced with the one held by the special value and the computation
continues from there.  It is like taking a snapshot of the execution
context at some moment in time and then, when desired, being able to
get back in time to that point.  If you like games, it is like saving
the game now (so you can work on your homework!) and then continuing
the game tomorrow or whenever you wish.  We will define the formal
semantics of \texttt{callcc} in the semantics module below.  For now,
we can desugar the \texttt{try-catch} construct into callcc: */

  rule try E catch(X) E'
    => callcc (fun $k -> (fun throw -> E)
                         (fun $v -> $k ((fun (X)::Id -> E') $v)))  [macro]
endmodule


/*@ \section{Semantics}

The semantics below is environment-based.  See the LAMBDA languages in
the tutorial, for examples of substitution-based definitions of
simple functional languages, or the definition of AGENT in the list of
examples for a more complex one.  We prefer an environment-based
definition here only because FUN has the variable address construct
\texttt{\&x}, which grabs the reference of variable \texttt{x}, and
this is easier to define in an environment-based style. */


module FUN-UNTYPED
  imports FUN-UNTYPED-SYNTAX
  imports PATTERN-MATCHING

/*@ \subsection{Configuration}

The \textsf{k}, \textsf{env}, and \textsf{store} cells are standard
(see, for example, the definition of LAMBDA++ or IMP++ in the \K
tutorial).  */

  configuration <T color="yellow"> 
                  <k color="green"> $PGM:Exp </k>
                  <env color="violet"> .Map </env>
                  <store color="white"> .Map </store>
                </T>


/*@ \subsection{Values and results}

We only define integers and Booleans as values here, but will add more
values later.  */

  syntax Val ::= Int | Bool
  syntax Vals ::= List{Val,","}
  syntax Exp ::= Val
  syntax KResult ::= Val


//@ \subsection{Lookup}

  rule <k> X:Id => V ...</k>
       <env>... X |-> L ...</env>
       <store>... L |-> V ...</store>


//@ \subsection{Arithmetic expressions}

  rule I1:Int + I2:Int => I1 +Int I2
  rule (I1:Int - I2:Int) => I1 -Int I2
  rule I1:Int * I2:Int => I1 *Int I2
  rule I1:Int / I2:Int => I1 /Int I2 when I2 =/=K 0
  rule I1:Int % I2:Int => I1 %Int I2 when I2 =/=K 0
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


/*@ \subsection{Functions and Closures}

Like in the environment-based semantics of LAMBDA++ in the \K
tutorial, functions evaluate to closures.  A closure includes the
current environment besides the function contents; the environment
will be used at execution time to lookup all the variables that appear
free in the function body (we want static scoping in FUN). */

  syntax Val ::= closure(Map,Cases)
  rule <k> fun Cases => closure(Rho,Cases) ...</k>  <env> Rho </env>

/*@ \paragraph{Note:} The reader may want to get familiar with
how the pre-defined pattern matching works before proceeding.  The best
way to do that is to consult \texttt{k/include/modules/pattern-matching.k}. */

/*@ We distinguish two cases when the closure is applied.  If the first
pattern matches, then we pick the first case: switch to the closed
environment, get the matching map and bind all its variables, and finally
evaluate the function body of the first case, making sure that the
environment is properly recovered afterwards.  If the first pattern
does not match, then we drop it and thus move on the next one. */

  rule <k> closure(Rho, P->E | _) V:Val
           => bindTo(getMatching(P,V)) ~> E ~> env(Rho') ...</k>
       <env> Rho' => Rho </env>  when isMatching(P,V)
  rule closure(_, (P->_ | Cases => Cases)) V:Val  when notBool isMatching(P,V)

/*@ Besides the generic decomposition rules for patterns and values,
we also want to allow \texttt{[head|tail]} matching for lists, so add
the following custom rule: */

  rule decomposeMatching(([H:Exp|T:Exp] => H,T),([V:Val,Vs:Vals] => V,[Vs]))


/*@ \subsection{Let and Letrec}

To highlight the similarities and differences between \texttt{let} and
\texttt{letrec}, we prefer to give them direct semantics instead of
to desugar them like in LAMBDA.  See the formal definitions of
\texttt{bindTo}, \texttt{bind}, and \texttt{assignTo} at the end of
this module.  Informally, \texttt{bindTo($\it Xs$,$\it Es$)} first
evaluates the expressions ${\it Es}\in\textit{Exps}$ in the current
environment (i.e., it is strict in its second argument), then it binds
the variables in ${\it Xs}\in\textit{Ids}$ to new locations and adds
those bindings to the environment, and finally writes the values
previously obtained after evaluating the expressions $\it Es$ to those
new locations; \texttt{bind($\it Xs$)} does only the bindings of
$\it Xs$ to new locations and adds those bindings to the environment;
and \texttt{assignTo($\it Xs$,$\it Es$)} evaluates the expressions
$\it Es$ in the current environment and then it writes the resulting
values to the locations to which the variables $\it Xs$ are already
bound to in the environment.

Therefore, ``\texttt{let $\it Xs$=$\it Es$ in $\it E$}'' first
evaluates $\it Es$ in the current environment, then adds new
bindings for $\it Xs$ to fresh locations in the environment, then
writes the values of $\it Es$ to those locations, and finally
evaluates \textit{E} in the new environment, making sure that the
environment is properly recovered after the evaluation of \textit{E}.
On the other hand, \texttt{letrec} does the same things but in a
different order: it first adds new bindings for $\it Xs$ to fresh
locations in the environment, then it evaluates $\it Es$ in the new
environment, then it writes the resulting values to their
corresponding locations, and finally it evaluates \textit{E} and
recovers the environment.  The crucial difference is that the
expressions $\it Es$ now see the locations of the variables
$\it Xs$ in the environment, so if they are functions, which is
typically the case with \texttt{letrec}, their closures will
encapsulate in their environments the bindings of all the bound
variables, including themselves (thus, we may have a closure value
stored at location \textit{L}, whose environment contains a binding of
the form $\textit{F} \mapsto \textit{L}$; this way, the closure can
invoke itself). */

  rule <k> let Bs in E
        => bindTo(ids(Bs),exps(Bs)) ~> E ~> env(Rho) ...</k>
       <env> Rho </env>

  rule <k> letrec Bs in E
        => bind(ids(Bs)) ~> assignTo(ids(Bs),exps(Bs)) ~> E ~> env(Rho)...</k>
       <env> Rho </env>

/*@ Recall that our syntax allows \texttt{let} and \texttt{letrec} to
take any expression in place of its binding.  This allows us to use
the already existing function application construct to bind names to
functions, such as, e.g., ``\texttt{let x y = y in ...}''.  The
desugaring macro in the syntax module uncurries such declarations, and
then the semantic rules above only work when the remaining bindings
are identifiers, so the semantics will get stuck on programs that
misuse the \texttt{let} and \texttt{letrec} binders. */


//@ \subsection{Conditional}

  rule if  true then E else _ => E
  rule if false then _ else E => E


/*@ \subsection{Tuples and Lists}

We have already declared the tuple and list constructs strict, so we
can assume that all their elements are evaluated.  For tuples, the
only thing left to do is to state that a tuple of values is also a
value.  For lists, we have to additionally give the semantics of
\texttt{cons}: */

// the "function" tag is currently needed due to a tool bug
  rule isVal({Vs:Vals}) => true  [function]
  rule isVal([Vs:Vals]) => true  [function]

  rule cons V:Val [Vs:Vals] => [V,Vs]


/*@ \subsection{References}
The semantics of references is self-explanatory.  Note that
\texttt{\&$X$} grabs the location of $X$ from the environment; this
operation would be harder to define in a substitution-based approach. */

  rule <k> & X => L ...</k>  <env>... X |-> L </env>
  rule <k> @ L => V ...</k>  <store>... L |-> V ...</store>
  rule <k> L := V:Val => V ...</k>  <store>... L |-> (_=>V) ...</store>

/*@ Sequential composition, which is needed only to accumulate the
side effects due to assignments, was strict in the first argument.
Once evaluated, its first argument is simply discarded. */

  rule V:Val; E => E


/*@ \subsection{Callcc}

As we know it from the LAMBDA++ tutorial,
call-with-current-continuation is quite easy to define in \K.  We
first need to define a special value wrapping an execution context,
that is, an environment saying where the variables should be looked up,
and a computation structure saying what is left to execute (in a
substitution-based definition, this special value would be even
simpler, as it would only need to wrap the computation
structure---see, for example, the substitution-based semantics of
LAMBDA++ in the tutorial).  Then \texttt{callcc} creates such a value
containing the current environment and the current remaining
computation, and passes it to its argument function.  When/If invoked,
the special value replaces the current execution context with its own
and continues the execution normally.  */

  syntax Val ::= cc(Map,K)
  rule <k> (callcc V:Val => V cc(Rho,K)) ~> K </k>  <env> Rho </env>
  rule <k> cc(Rho,K) V:Val ~> _ => V ~> K </k>  <env> _ => Rho </env>


//@ \subsection{Auxiliary operations}

/*@ \subsubsection{Environment recovery}

The environment recovery operation is the same as for the LAMBDA++
language in the \K tutorial and many other languages provided with the
\K distribution.  */

  syntax K ::= env(Map)
  rule (env(_) => .) ~> env(_)  [anywhere]   // tail recursion
  rule <k> _:Val ~> (env(Rho) => .) ...</k> <env> _ => Rho </env>  [structural]

/*@ \subsubsection{\texttt{bindTo}, \texttt{bind} and \texttt{assignTo}}

The meaning of these operations has already been explained when we
discussed the \texttt{let} and \texttt{letrec} language constructs above. */

  syntax K ::= bindTo(Ids,Exps)         [strict(2)]
             | bindTo(Map)
             | bind(Ids)

  rule bindTo(Xs:Ids,Vs:Vals) => bindTo(getMatching(Xs,Vs))

  rule bindTo(.Map) => .  [structural]
  rule <k> bindTo((X:Id |-> V:Val => .) _) ...</k>
       <env> Rho => Rho[L/X] </env>
       <store>... . => L |-> V ...</store>
    when fresh(L:Int)  [structural]

  rule bind(.Ids) => .                  [structural]
  rule <k> bind(X:Id,Xs => Xs) ...</k>
       <env> Rho => Rho[L/X] </env>
    when fresh(L:Int)                   [structural]

  syntax K ::= assignTo(Ids,Exps)  [strict(2)]

  rule <k> assignTo(.Ids,.Vals) => . ...</k>            [structural]
  rule <k> assignTo((X:Id,Xs => Xs),(V:Val,Vs => Vs)) ...</k>
       <env>... X |-> L ...</env>
       <store>... . => L |-> V ...</store>              [structural]

/*@ \subsubsection{Getters}

The following auxiliary operations extract the list of identifiers
and of expressions in a binding, respectively. */

  syntax Ids ::= ids(Bindings)  [function]
  rule ids(.Bindings) => .Ids
  rule ids(X:Id=_ and Bs) => X,ids(Bs)

  syntax Exps ::= exps(Bindings)  [function]
  rule exps(.Bindings) => .Exps
  rule exps(_:Id=E and Bs) => E,exps(Bs)

endmodule
