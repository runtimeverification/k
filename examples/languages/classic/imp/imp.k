//
// WARNING
//
// This is a heavily commented K definition, part of the K
// tutorial.  To turn off the comments, you can do one of the
// following (or remove them manually):
//   1) Use an editor which can hide or color comments (K uses
//      standard comments)
//   2) Run the K pre-processor (kpp) on this file to remove all
//      comments.
// Moreover, since the purpose of the tutorial is to teach you K, the
// language definition below may not be configured optimally as is.
// For example, the initial configuration has no configuration variables.
// Thus, some example programs may not run well with the provided
// configuration.  You will be required to configure the K definition
// appropriately and then rekompile it in order to run those programs.

/*!
\setlength{\parindent}{1em}
\title{IMP}
\author{Grigore Ro\c{s}u (\texttt{grosu@illinois.edu})}
\organization{University of Illinois at Urbana-Champaign}
*/

/*@ \section{Abstract}
This is the \K semantic definition of the classic IMP language.
IMP is considered a folklore language, without an official inventor,
and has been used in many textbooks and papers, often with slight
syntactic variations and often without being called IMP\@.  It includes
the most basic imperative language constructs, namely basic constructs
for arithmetic and Boolean expressions, and variable assignment,
conditional, while loop and sequential composition constructs for statements.

\paragraph{Note:}{
Since IMP is so simple, we will use its semantics as an opportunity to
explain some of the main features of the \K  prototype tool.  Other
features will be explained in other \K definitions coming as part of
this distribution.  For a quick introduction to the \K prototype, you
are referred to the README file at the root of this
distribution.  If you are interested in reading more about \K, please
check the following paper:
\begin{quote}
Grigore Ro\c su, Traian-Florin \c Serb\u anu\c t\u a:
\href{http://dx.doi.org/10.1016/j.jlap.2010.03.012}
     {An overview of the K semantic framework}.

Journal of Logic and Algebraic Programming, 79(6): 397-434 (2010)
\end{quote}
}

\paragraph{Note:}{
\K follows the
\href{https://en.wikipedia.org/wiki/Literate_programming}{literate
programming} approach.  The various semantic features defined in a \K
module can be reordered at will and can be commented using normal
comments like in C/C++/Java.  If those comments start with
`\texttt{@}' preceded by no space (e.g.,
`\texttt{//{@} {\textbackslash}section\{Variable declarations\}}'
or
`\texttt{/*{@} {\textbackslash}section\{Variable declarations\} {*}/}')
then they are interpreted as formal \LaTeX\ documentation by the
\texttt{kompile} tool when used with the option \texttt{-\,\!-pdf}
(or \texttt{-\,\!-latex}).
While comments are useful in general, they can annoy the expert user
of \K.  To turn them off, you can do one of the following (unless you
want to remove them manually): (1) Use an editor which can hide or
color conventional C-like comments; or (2) Run the \K pre-processor
(kpp) on the ASCII .k file, which outputs (to stdout) a variant of the
\K definition with no comments.
}

\paragraph{Note:}{
The \K tool provides modules for grouping language features.  While
there are no rigid requirements or even guidelines on how to group
features, we often put the language syntax in a separate module, so we
can experiment with parsing programs before we attempt to give our
language a semantics.  In the case of IMP, we call its syntax module
\texttt{IMP-SYNTAX} and its semantics module \texttt{IMP}.  To compile
the IMP definition into Maude, pass the \texttt{imp.k}
(extension is optional) file to \texttt{kompile}:
\begin{verbatim}
$ kompile imp.k
\end{verbatim}
To compile it to a PDF document for visualization, use the command:
\begin{verbatim}
$ kompile imp.k --pdf
\end{verbatim}
To run programs, simply pass the program to \texttt{krun} in the
directory where \texttt{imp.k} is:
\begin{verbatim}
$ krun programs/sum.imp
\end{verbatim}
In general, the above commands work as shown for any language, say
LANG, provided that you replace \texttt{IMP} by \texttt{LANG} and
\texttt{imp} by \texttt{lang}, and provided that you type these
commands in the directory where your language definition
\texttt{lang.k} is.  If you want to use different naming
conventions or to call these commands from other places, then type
``\texttt{kompile -\,\!-help}'' and ``\texttt{krun -\,\!-help}'' for
instructions.
}

\section{What You Will Learn Here}

\begin{itemize}
\item Basic notions about \K and how to write simple \K definitions.
\item How to define a simple programming language in \K.
\item How to use the \K tool for compilation to Maude and to \LaTeX/PDF.
\item How to use the \K tool to execute programs using the semantics.
\item How to customize the initial configuration using configuration
variables and initializing them with \texttt{krun}.
\end{itemize}
*/


module IMP-SYNTAX
/*@ \section{Syntax}
This module defines the syntax of IMP\@.
Syntax in \K is defined using the familiar BNF notation, with
terminals enclosed in quotes and nonterminals starting with capital
letters, except for the builtin nonterminals which start with
``\textit{\#}''.  To ease reading, the quotes around the terminals are
not displayed in the generated PDFs.  Productions can have attributes,
which can define the evaluation strategy of the corresponding
constructs (the \texttt{strict} and \texttt{seqstrict} attributes), or
help the parser with operator precedences and grouping (the
\texttt{prec} and \texttt{gather} attributes), or instruct the PDF
generator how to display the various constructs (the \texttt{latex}
attribute), etc.

The following constructs are given the expected strictness attributes,
except for \texttt{<=} and \textsf{and}, for demonstration purposes.
The former is defined to be \texttt{seqstrict}, which means that it
evaluates its arguments in order, from left to right.  The
\texttt{strict} operators can evaluate their arguments in any (fully
interleaved) orders.  The latter is only strict in its first argument,
because we will give it a short-circuited semantics (its second
argument will only be evaluated when the first evaluates to true).
The parsing attributes, which are not displayed in the generated PDFs
(also to ease reading), are taken over from Maude; please consult
Maude's manual for their meaning.  For example, \texttt{prec(...)}
defines a precedence for the corresponding syntactic construct, which
is taken into account when parsing programs and rules (the lower the
precedence the tighter the binding).  Also, \texttt{gather(...)} is
used for grouping reasons; for example, \texttt{gather(E e)} means
left-associative and \texttt{gather(e E)} means right-associative.
The \K tool also allows us to associate \LaTeX\ attributes to
constructs, telling the PDF generator how to display them.  For
example, \texttt{<=} has the attribute
\texttt{latex("\{\#1\}\textbackslash{leq}\{\#2\}")}, which makes it be
displayed as $\leq$ everywhere in the generated PDF.  Currently, the
\K tool allows parentheses to be used for grouping (e.g.,
``\texttt{while (x>=0) (x:=x/2; y:=x)}''). */

  syntax AExp ::= Int | Id
                | AExp "+" AExp    [prec(33) gather (E e) strict]
                | AExp "/" AExp    [prec(31) gather (E e) strict]
  syntax BExp ::= Bool
                | AExp "<=" AExp   [prec(37) seqstrict latex("{#1}\leq{#2}")]
                | "not" BExp       [prec(53) strict]
                | BExp "and" BExp  [prec(55) strict(1)]
  syntax Stmt ::= "skip"
                | Id ":=" AExp    [prec(80) strict(2)]
                | Stmt ";" Stmt    [prec(100) gather(e E)]
                | "if" BExp
                  "then" Stmt
                  "else" Stmt      [prec(85) strict(1)]
                | "while" BExp
                  "do" Stmt        [prec(85)]

/*@ An IMP program declares a set of variables and then executes a
statement in the state obtained after initializing all those variables
to 0.  IMP does not allow variable declarations anywhere else except
through this construct, at the top-level of the program.  Other
languages provided with this \K distribution (see, e.g., the IMP++
language) remove this top-level program construct of IMP and add
instead variable declaration as a statement construct, which can be
used anywhere in the program, not only at the top level.
\K provides builtin support for generic syntactic lists: 
$\textit{List}\{\textit{Nonterminal},\textit{terminal}\}$ stands for
\textit{terminal}-separated lists of \textit{Nonterminal} elements;
the lists can also be empty, that is, IMP programs declaring no
variable are also allowed (e.g., ``\texttt{var; skip}'').  To
instantiate and use the \K builtin lists, you should alias each
instance with a (typically fresh) nonterminal in your syntax, like we
do below with the \textit{Ids}. */

  syntax Pgm ::= "var" Ids ";" Stmt  [prec(110)]
  syntax Ids ::= List{Id,","}

end module

/*@ Before we move to the \K semantics, we would like to make some
clarifications regarding the \K syntactic declarations and the current
builtin parser in general.  First, you should not expect magic from
these in terms of parsing.  While the \K parser can parse many
non-trivial languages (see, for example, the KOOL language), it was
never meant to be a substitute for real parsers.  We often call the
syntax defined in \K ``the syntax of the semantics'', to highlight the
fact that its role is to serve as a convenient notation when writing
the semantics, not as a means to define concrete syntax of arbitrarily
complex programming languages.  See the KERNELC language for an
example on how to connect an external parser for concrete syntax to
the \K tool.  Second, since we use the same \K parser to also parse
the semantic rules below, we use the same \texttt{syntax} keyword to
define additional syntax needed exclusively for the semantics.  We
will discuss other particularities of the \K syntax on a by-need
basis, as we define more complex languages (see other \K language
definitions coming with this distribution of the \K tool). */

module IMP
  imports IMP-SYNTAX
/*@ \section{Semantics}
This module defines the semantics of IMP\@.  
Before you start adding semantic rules to a \K definition, you need to
define the basic semantic infrastructure consisting of definitions for
{\em values/results} and the {\em configuration}.  The semantic rules,
or the {\em \K rules}, are of two types: {\em structural} and
{\em computational}.  Intuitively, structural rules rearrange the
configuration so that computational rules can apply.  Structural rules
therefore do not count as computational steps.  A \K semantics can be
thought of as a generator of transition systems or Kripke structures,
one for each program.  It is only the computational rules that create
steps, or transitions, in the corresponding transition systems or
Kripke structures, the structural rules being unobservable at this
level.  By default, rules are assumed computational.  If you want to
explicitly make a rule structural, then you should include the
tag/attribute \texttt{structural} in square brackets right after the
rule.  These attributes may be taken into account by different \K
tools, so it is highly recommended to spend a moment after each rule
and think whether you want it to be structural or computational.  */

/*@ \subsection{Values and results}
IMP only has two types of values, or results of computations: integers
and Booleans.  We here use the \K builtin variants for both of them,
noting that you are free to define your own values if these are not
suitable for your language (e.g., the builtin integers and operations
on them are arbitrary precision, etc.).
The file \texttt{k-framework/core/maude/lib/pl-builtins.maude}
contains the (Maude) definitions of all the current builtins offered
by the \K tool.  Although unnecessary here, it is insightful and useful
to understand the relationship between your language's values and other
syntactic categories.  It is often the case that values form a
subset of the existing language syntax, like here, but sometimes that
is not immediately obvious and sometimes even not true by default (for
example, when defining functional languages we may add closures as
values, even though closures were not expressions in the original
language).  When that happens, in order for the semantics to be
given smoothly and uniformly you may need to extend your language's
original syntactic categories with the new values.  This is not needed
for our IMP semantics here, since its values are trivial and already
part of the original syntax.  Nevertheless, we still have to tell the
\K tool that it should interpret our intended values as results of
computations (note that this is not automatic, since sometimes other
syntactic categories are results; e.g., types when defining a type system). */

  syntax KResult ::= Int | Bool

/*@ Before we move to the definition of the IMP configuration, we
would like to recall a few general facts about \K, particularly about
its computation structures and the relationship between strictness and
\K results.  Computation structures, called {\em computations} for
simplicity, extend the abstract syntax of your language with a list
structure using $\kra$ (read  ``followed by'' or ``and then'', and
written \texttt{\texttildelow>} in ASCII) as a separator.  \K provides
a distinguished sort, $K$, for computations.  The extension of the
abstract syntax of your language into computations is done
automatically when you declare constructs using the \texttt{syntax}
keyword, so the \K semantic rules can uniformly operate only on 
terms of sort $K$.  The intuition for computation structures of the
form $t_1 \kra t_2 \kra \cdots \kra t_n$ is that the listed tasks are
to be processed in order.  The initial computation typically contains
the original program as its sole task, but rules can then modify it
into task sequences.  The strictness attributes, used as
annotations to language constructs, actually correspond
to rules over computations.  For example, the \texttt{strict(2)}
attribute of the assignment statement above corresponds to the
following two structural rules, which are generated automatically by
the \K tool:
$$
\begin{array}{l}
X \texttt{:=}\ E \ \ \Rightarrow \ \ E \kra X \ \texttt{:=}\ \square
\ \ \textsf{if} \ \ E\not\in\KResult \\
E \kra X \texttt{:=}\ \square \ \ \Rightarrow \ \ X\ \texttt{:=}\ E
\ \ \textsf{if} \ \ E\in\KResult
\end{array}
$$
The first rule above pulls $E$ out of its context for processing when it is
not a result, and the second rule plugs it back into its context once
it becomes a result (after rewriting with other rules in the semantics).
We call rules of the first type above {\em heating rules} and rules of
the second type {\em cooling rules}.  Similar rules are generated for
other arguments in which operations are strict.  When operations are
strict only in some of their arguments, the corresponding positions of
the arguments in which they are strict are explicitly enumerated in
the argument of the \texttt{strict} attribute, e.g.,
\texttt{strict(2)} like above, or \texttt{strict(2 3)} for an
operation strict in its second and third arguments, etc.
If an operation is simply declared \texttt{strict} then it means that
it is strict in all its arguments.  The same holds true for sequential
strictness, declared with the keyword \texttt{seqstrict}.  In both
cases, we assume the arguments enumerated from left-to-right.  In the
case of \texttt{strict} the order is irrelevant, but it is relevant
for \texttt{seqstrict}.  For example, the default heating/cooling rules
associated to the sequentially strict \texttt{<=} construct above are:
$$
\begin{array}{l}
E_1 \leq E_2 \ \ \Rightarrow \ \ E_1 \kra \square \leq E_2
\ \ \textsf{if} \ \ E_1\not\in\KResult \\
E_1 \kra \square \leq E_2 \ \ \Rightarrow \ \ E_1 \leq E_2
\ \ \textsf{if} \ \ E_1\in\KResult \\
E_1 \leq E_2 \ \ \Rightarrow \ \ E_2 \kra E_1 \leq \square
\ \ \textsf{if} \ \ E_1\in\KResult \ \wedge \ E_2 \not\in\KResult \\
E_2 \kra E_1 \leq \square \ \ \Rightarrow \ \ E_1 \leq E_2
\ \ \textsf{if} \ \ E_1\in\KResult \ \wedge \ E_2 \in \KResult
\end{array}
$$
Note that $E_2$ above is pulled for evaluation only after $E_1$ is
fully evaluated.  Similar heating/cooling rules are also automatically
associated to \K (evaluation) context declarations in more complex
languages.  It is easy to see that such heating/cooling rules can
easily lead to non-determinism, since the same term may be heated many
different ways; these different evaluation orders may lead to
different behaviors in some languages (not in IMP, because its
expressions do not have side effects, but we will experiments with
non-determinism in its successor, IMP++).

Thus the values/results are needed to know when to stop
applying the heating rules and then to start applying the cooling
rules.  As values carry semantic, language dependent meaning, they
cannot be automatically inferred, so you cannot avoid this step in
which you tell the tool which are the values/results of your
computations.  Note that in the theory of \K you do not need to
explicitly declare values/results, because the heating/cooling rules
are unconditional and reversible to each other, the actual semantic
rules applying {\em modulo} them.  However, reversible rules lead to
non-termination in the tool, so they had to be restricted. */


/*@ \subsection{Configuration}
A \K configuration serves as a backbone for the process of {\em configuration
abstraction} which allows users to only mention the relevant cells in each
semantic rule, the rest of the configuration context being inferred
automatically.  The importance of configuration abstraction will
become clear when we define more complex languages (even in IMP++).
IMP does not need it.

The configuration of IMP is trivial: it only contains two cells, one
for the computation and another for the state.  For good encapsulation
and clarity, we place the two cells inside another cell, the ``top'' cell
which is labeled \textsf{T}. */

  configuration <T color="yellow">
                  <k color="green"> $PGM:K </k>
                  <state color="red"> .Map </state>
                </T>
// Replace the above <state/> cell with the following when you want to pass
// an initial state through krun; see program programs/sum-novars.imp.
//                  <state color="red"> $STATE:Map </state>
// Make sure you rekompile the definition before calling krun.

/*@ The configuration variable {\em \$PGM} tells the \K tool where to
place the program.  More precisely, the command
``\texttt{krun program}'' parses the program and places the resulting
\K abstract syntax tree in the \textsf{k} cell before invoking the
semantic rules described in the sequel.  The ``$\kdot$'' in the
\textsf{state} cell, written \texttt{.Map} in ASCII in the
\texttt{imp.k} file, is \K's way to say ``nothing''.  Technically, it
is a constant which is the unit, or identity, of all maps in \K
(similar dot units exist for other \K structures, such as lists, sets,
multi-sets, etc.).  Sometimes we want to customize the initial
configuration before executing a program.  Then we can use
custom configuration variables, whose name starts with {\em \$} like
that of {\em \$PGM}.  For example, we can replace the
$\kdot$ contents of the \textsf{state} cell with configuration
map variable {\em \$STATE}.  This allows you to pass your desired
initial state to \texttt{krun} in addition to the program, such as in
the following command requesting \texttt{krun} to execute
a program in a state binding $n$ to 0 and $s$ to 10:
\begin{verbatim}
krun programs/sum-novars.imp --STATE="n|->0 s|->10"
\end{verbatim}
*/

/*@ \subsection{Arithmetic expressions}
The \K semantics of each arithmetic construct is defined below. */

/*@ \subsubsection{Variable lookup}
A program variable $X$ is looked up in the state by matching a binding
of the form $X \mapsto I$ in the state cell.  If such a binding does not
exist, then the rewriting process will get stuck.  Thus our semantics of
IMP disallows uses of uninitialized variables.  Note that the variable
to be looked up is the first task in the \textsf{k} cell (the cell is
closed to the left and torn to the right), while the binding can be
anywhere in the \textsf{env} cell (the cell is torn at both sides). 
In \K you can name rules; for example, we named the lookup rule below
\texttt{lookup}.  The rule names help to increase the clarity of your
definitions and can be used by different \K tools in different ways. */

  rule [lookup]: <k> X:Id => I ...</k> <state>... X |-> I ...</state>

/*@
Before we continue, we would like to remind the reader that the
compact \K rule above, written in ASCII notation as
\begin{verbatim}
rule <k> X => I ...</k> <state>... X |-> I ...</state>
\end{verbatim}
is desugared by the tool into an ordinary
rewrite rule:
\begin{verbatim}
rule <k> X ~> Rest </k> <state> Before (X |-> I) After </state>
  => <k> I ~> Rest </k> <state> Before (X |-> I) After </state>
\end{verbatim}
Except for its true concurrency semantics, which relies on what is
explicitly declared as shared and what is not, the semantics of \K can
actually be reduced to the semantics of rewriting logic with only
rules of the form
$$
\textit{left} \ \Rightarrow\ \textit{right} \ \ \textsf{if} \ \textit{condition}
$$
with \textit{condition} a Boolean condition (involving no rewrite
steps). */

/*@ \subsubsection{Arithmetic operators}
There is nothing special about these, except that the rule for division
has a side condition.  The operations with subscripts in the right-hand
sides of the rules are builtin and come with the corresponding builtin
sort; they are actually written like \texttt{+Int} in ASCII, but they
have \LaTeX\ attributes to be displayed like $+_{\it Int}$ in the
generated PDF document. Note that the variables appearing in these
rules have integer sort.  That means that these rules will only be
applied after the arguments of the  arithmetic constructs are fully
evaluated to \K results; this will happen thanks to their strictness
attributes declared as annotations in the syntax module above.  For
demonstration purposes, we do not label the trivial rules below for
arithmetic and Boolean constructs. 

For the rest of this \K definition, recall that \K is a
context-insensitive rewriting framework, that is, rewrite rules can
apply wherever they match.  If you want a particular rewrite step to
not take place unless it is in the right place, then you have to add
more context to the rule so that it will not match.  For example, the
first rule below will rewrite \texttt{3+7} to \texttt{10} no matter
where it is located in the program.  If you want such reductions
to only take place when they reach a position which can be evaluated
according to the declared (through strictness attributes or evaluation
contexts) evaluation strategies of the various language constructs,
then you should modify the rules below to also match the beginning of
the \textsf{k} cell (e.g., ``\texttt{<k> I1 + I2 => I1 +Int I2 ...</k>}'',
etc.).  Note that this is in sharp contrast to structural operational
semantics (SOS), where one needs to explicitly give permission
(through conditional rules) to reductions inside language constructs'
arguments.  In general, we prefer to not inhibit the application of
rewrite steps when unnecessary, because that also inhibits \K's
potential for concurrent rewriting, but some language designers may
get confused (or not like it) even when safe rewrites are applied in
places of the program where they were not supposed to.  Those are free
to modify the rules below to always match at the top of the \textsf{k}
cell. */

  rule I1:Int + I2:Int => I1 +Int I2
  rule I1 / I2 => I1 /Int I2  when I2 =/=Int 0 

/*@ \subsection{Boolean expressions}
The rules below are straightforward.  Note the short-circuited semantics
of \textsf{and}; this is the reason we annotated the syntax of
\textsf{and} with the \K attribute \texttt{strict(1)} instead of \texttt{strict}.
The particular name of a variable in a rule is sometimes irrelevant,
as it happens in the second rule for \texttt{and} below.  \K allows us
to use anonymous variables, written as underscores like in Prolog. */

  rule I1 <= I2 => I1 <=Int I2
  rule not(T:Bool) => notBool T
  rule true and B:BExp => B
  rule false and _ => false

/*@ \subsection{Statements}
There is one rule per statement construct except for the conditional,
which needs two rules. */

/*@ \subsubsection{Skip}
The \texttt{skip} is simply dissolved.  The $\kdot$ below is the unit
of the computation list structure, that is, the empty task.  The \K
tool structurally erases it from the computation structure, without
considering its erasure as a computational step.  You can make this
rule structural (using the attribute \texttt{structural}, as seen
below in the rule for sequential composition) if you do not want it to
count as a computational step. */

  rule [skip]: skip => .

/*@ \subsubsection{Assignment}
The assigned variable is updated in the state.  The variable is expected
to be declared, otherwise the semantics will get stuck.  At the same time,
the assignment is dissolved. */

  rule [assignment]:
    <k> X := I:Int => . ...</k> <state>... X|->(_ => I) ...</state>

/*@ \subsubsection{Sequential composition}
Sequential composition is simply structurally translated into \K's
builtin task sequentialization operation.  You can make this rule
computational (i.e., remove the \texttt{structural} attribute) if you
want it to count as a computational step.  Recall that the semantics
of a program in a programming language defined in \K is the transition
system obtained from the initial configuration holding that program
and counting only the steps corresponding to computational rules as
transitions (i.e., hiding the structural rules as unobservable, or
internal steps). */

  rule [sequential]: S1:K ; S2:K => S1 ~> S2  [structural]

/*@ \subsubsection{Conditional}
The conditional statement has two semantic cases, corresponding to
when its condition evaluates to \texttt{true} or to \texttt{false}.
Recall that the conditional was annotated with the attribute
\texttt{strict(1)} in the syntax module above, so only its first
argument is allowed to be evaluated. */

  rule [if-true]:  if true then S:K else _ => S
  rule [if-false]: if false then _ else S => S

/*@ \subsubsection{While loop}
We give the semantics of the \texttt{while} loop by unrolling.
Note that we preferred to make the rule below structural. */

  rule [while]:
    while B do S => if B then (S ; while B do S) else skip
    [structural]

/*@ \subsection{Programs}
The semantics of an IMP program is that its body statement is executed
in a state initializing all its global variables to 0.  Since \K's
syntactic lists are internally interpreted as cons-lists (i.e., lists
constructed with a head element followed by a tail list), we need to
distinguish two cases, one when the list has at least one element and
another when the list is empty.  In the first case we initialize the 
variable to 0 in the state, but only when the variable is not already
declared (all variables are global and distinct in IMP).  We prefer to
make the second rule structural, thinking of dissolving the residual
empty \texttt{var} declaration as a structural cleanup rather than as
a computational step.  The use of the ``$\kdot$'' in the second rule
below, written ``\texttt{.Ids}'' in the ASCII imp.k file, is not
necessary.  We could have written ``\texttt{var; S}'' instead of
``\texttt{var .Ids; S}'' and the \K tool would parse it and kompile
the definition correctly, as it uses the same parser used for parsing
programs also to parse the semantics.  However, we typically prefer to
explicitly write the ``nothing'' values in the semantics, for clarity;
the \K parser has been extended to accept these.  Note that the rules
below match the entire \textsf{k} cell, because \texttt{var\_;\_} is
the top-level program construct in IMP, so there is nothing following
it in the computation cell.  The anonymous variable in the first rule
stands for the second argument of this top-level program construct,
not for the rest of the computation. */

  rule [program-still-vars]:
       <k> var (X,Xs:Ids => Xs); _ </k>
       <state> Rho:Map (. => X |-> 0) </state>
    when notBool(X in keys(Rho))
  rule [program-no-vars]: <k> var .Ids; S => S </k>  [structural]
end module
