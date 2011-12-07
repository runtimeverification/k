// Warning: this is a heavily commented K definition.  To turn off
// the comments, you can do one of the following (or remove them manually):
// 1) Use an editor which can hide or color comments (K uses standard comments)
// 2) Run the K pre-processor (kpp) on this file to remove all comments.

module IMP-SYNTAX
/*@ \K provides modules for grouping syntactic and semantic features
of language definitions.  While there are no rigid requirements or
even guidelines on how to group features, we often put the syntax of
languages in separate modules, so we can experiment with parsing
programs before we attempt to give our languages semantics. */

/*@ \section{Syntax}
Syntax in \K is defined using the familiar BNF notation, with
terminals enclosed in quotes and nonterminals starting with capital
letters, except for the builtin nonterminals which start with
``\textit{\#}''.  To ease reading, the quotes around the terminals are
not displayed in the generated PDFs.  Productions can have attributes,
which can define the evaluation strategy of the corresponding
constructs (the \texttt{strict} attribute), or help the parser with
operator precedences and grouping (the \texttt{prec} and
\texttt{gather} attributes), or instruct the PDF generator how to
display the various constructs (the \texttt{latex} attribute), etc. 
The following constructs are given the expected strictness attributes,
except for \textsf{and}, which is only strict in its first argument,
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
The \K tool also allows us to associate Latex attributes to
constructs, telling the PDF generator how to display them.  For
example, the \texttt{<=} construct below has the attribute
\texttt{latex("\{\#1\}\textbackslash{leq}\{\#2\}")}, which makes it be
displayed as $\leq$ everywhere in the generated PDF.  Currently, the
\K tool allows parentheses to be used for grouping (e.g.,
``\texttt{while (x>=0) (x:=x/2; y:=x)}''). */

  syntax AExp ::= #Int | #Id
                | AExp "+" AExp    [:prec(33) gather (E e) strict:]
                | AExp "/" AExp    [:prec(31) gather (E e) strict:]
  syntax BExp ::= #Bool
                | AExp "<=" AExp   [:prec(37) seqstrict latex("{#1}\leq{#2}"):]
                | "not" BExp       [:prec(53) strict:]
                | BExp "and" BExp  [:prec(55) strict(1):]
  syntax Stmt ::= "skip"
                | #Id ":=" AExp    [:prec(80) strict(2):]
                | Stmt ";" Stmt    [:prec(100) gather(e E):]
                | "if" BExp
                  "then" Stmt
                  "else" Stmt      [:prec(85) strict(1):]
                | "while" BExp
                  "do" Stmt        [:prec(85):]

/*@ An IMP program declares a set of variables and then executes a
statement in the state obtained after initializing all those variables
to 0.  The IMPPP language removes this top-level program construct of
IMP and adds instead variable declaration as a statement construct,
which can be used anywhere in the program, not only at the top level.
\K provides builtin support for generic syntactic lists: 
$\textit{List}\{\textit{Nonterminal},\textit{terminal}\}$ stands for
\textit{terminal}-separated lists of \textit{Nonterminal} elements;
the lists can also be empty, that is, IMP programs declaring no
variable are also allowed (e.g., ``\texttt{var; skip}'').  To
instantiate and use the \K builtin lists, you should alias each
instance with a (typically fresh) nonterminal in your syntax, like we
do below with the \textit{Ids}. */

  syntax Pgm ::= "var" Ids ";" Stmt  [:prec(110):]
  syntax Ids ::= List{#Id,","}

/*@ Before we move to the \K semantics, we would like to make some
clarifications regarding the \K syntactic declarations and its builtin
parser in general.  First, you should not expect magic from these in
terms of parsing.  While the \K parser can parse many non-trivial
languages (see, for example, the KOOL language), it was never meant to
be a substitute for real parsers.  We often call the syntax defined in
\K ``the syntax of the semantics'', to highlight the fact that its
role is to serve as a convenient notation when writing the semantics,
not as a means to define concrete syntax of arbitrarily complex
programming languages.  See the KERNELC language for an example on how
to connect an external parser for concrete syntax to the \K tool.
Second, since we use the same \K parser to also parse the semantic
rules below, we use the same \texttt{syntax} keyword to define
additional syntax needed exclusively for the semantics.  We will
discuss other particularities of the \K syntax on a by-need basis, as
we define more complex languages (see other \K language definitions
coming with this distribution of the \K tool). */
end module

module IMP
  imports IMP-SYNTAX
/*@ \section{Semantics}
This module defines the semantics of IMP\@.  
Before you start adding semantic rules to a \K definition, you need to
define the basic semantic infrastructure consisting of definitions for
{\em values/results} and the {\em configuration}. */

/*@ \subsection{Values and results}
IMP only has two types of values: integers and Booleans.  We here use
the \K builtin variants for both of them, noting that you are free to
define  your own values if you don't like the builtins (e.g., the
builtin integers and operations on them are arbitrary precision, etc.). */

  syntax Val ::= #Int | #Bool

/*@ Although unnecessary here, it is insightful and useful to
understand the relationship between your language's values and other
syntactic categories.  It is often the case that values form a
subset of the existing language syntax, like here, but sometimes that
is not immediately obvious and sometimes even not true by default (for
example, when defining functional languages we may add closures as
values, even though closures were not expressions in the original
language).  When that is the case, in order for the semantics to be
given smoothly and uniformly, you may need to extend your language's
original syntactic categories with the new values.  This is not needed
for our IMP semantics here, since its values are trivial and already
part of the original syntax.

We have to tell the \K tool that it should interpret values as results
of computations (note that this is not automatic, since sometimes
other syntactic categories are results; e.g., types when defining a
type system).  In this case, since IMP is so simple, we could have
also directly said that integers and Booleans are \K results, without
declaring the syntactic category \textit{Val}.  In general, it is good
practice to add the values of your language as a separate syntactic
category and then instruct the \K tool that those are the results of
your computations.  The main reason for doing so is that the values of
your language will stay the same no matter what semantic style you
choose (thus you make your definition more generic and less dependent
on \K). */

  syntax KResult ::= Val

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
keyword, so the \K semantic rules can now uniformly operate only on 
terms of sort $K$.  The intuition for computation structures of the
form $t_1 \kra t_2 \kra \cdots \kra t_n$ is that the listed tasks are
to be processed in order.  The initial computation typically contains
the original program as its sole task, but rules can then modify it
into sequences of tasks.  The strictness attributes that we use as
syntactic annotations to language constructs in \K actually correspond
to rules over computations.  For example, the \texttt{strict(2)}
attribute of the assignment statement above corresponds to the
following two rules, which are generated automatically by the \K tool:
$$
\begin{array}{l}
X \texttt{:=}\ E \ \ \Rightarrow \ \ E \kra X \ \texttt{:=}\ \square
\ \ \textsf{if} \ \ E\not\in\KResult \\
E \kra X \texttt{:=}\ \square \ \ \Rightarrow \ \ X\ \texttt{:=}\ E
\ \ \textsf{if} \ \ E\in\KResult
\end{array}
$$
The first rule pulls $E$ out of its context for processing when it is
not a result, and the second rule plugs it back into its context once
it becomes a result (after rewriting with other rules in the semantics).
We call rules of the first type above {\em heating rules} and rules of
the second type {\em cooling rules}.  Similar rules are generated for
other \K (evaluation) context declarations in more complex languages.

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
become clear when we define more complex languages (even in IMPPP).
IMP does not need it.

The configuration of IMP is trivial: it only contains two cells, one
for the computation and another for the state.  For good encapsulation
and clarity, we place the two cells inside another cell, the ``top'' cell
which is labeled $\top$.  The configuration variable {\em \$PGM} tells
the \K tool where to place the program after parsing.  The ``$\kdot$''
in the \textsf{state} cell is \K's way to say ``nothing''.
Technically, it is a constant which is the unit (or identity) of all
the list, set, multiset, etc., structures in \K.  */

  configuration <T color="yellow">
                  <k color="green"> $PGM:Pgm </k>
                  <state color="red"> .Map </state>
                </T>
// Replace the above <state/> cell with the following when you want to pass
// an initial state through krun; see program programs/sumPgm-novars.imp.
//                  <state color="red"> $STATE:Map </state>


/*@ \subsection{Arithmetic expressions}
The \K semantics of each arithmetic construct is defined below.
We need to do nothing for those arithmetic expression constructs which
are already values, namely for integers and Booleans, because they are
already evaluated. */

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

  rule [lookup]: <k> X:#Id => I ...</k> <state>... X |-> I ...</state>

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
  => <k> I         </k> <state> Before (X |-> I) After </state>
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
have Latex attributes to be displayed like $+_{\it Int}$ in the
generated PDF document. Note that the variables appearing in these
rules have integer sort.  That means that these rules will only be
applied after the arguments of the  arithmetic constructs are fully
evaluated to \K results; this will happen thanks to their strictness
attributes declared as annotations in the syntax module above.  For
demonstration purposes, we do not label the trivial rules below for
arithmetic and Boolean constructs. */

  rule I1:#Int + I2:#Int => I1 +Int I2
  rule I1 / I2 => I1 /Int I2  if I2 =/=Bool 0 

/*@ \subsection{Boolean expressions}
The rules below are straightforward.  Note the short-circuited semantics
of \textsf{and}; this is the reason we annotated the syntax of
\textsf{and} with the \K attribute \texttt{strict(1)} instead of \texttt{strict}.
The particular name of a variable in a rule is sometimes irrelevant,
as it happens in the second rule for \texttt{and} below.  \K allows us
to use anonymous variables, written as underscores like in Prolog. */

  rule I1 <= I2 => I1 <=Int I2
  rule not(T:#Bool) => notBool T
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
    <k> X := I:#Int => . ...</k> <state>... X|->(_ => I) ...</state>

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

  rule [sequential]: S1:Stmt ; S2:Stmt => S1 ~> S2 [:structural:]

/*@ \subsubsection{Conditional}
The conditional statement has two semantic cases, corresponding to
when its condition evaluates to \texttt{true} or to \texttt{false}. */

  rule [if-true]:  if true then S:Stmt else _ => S
  rule [if-false]: if false then _ else S => S

/*@ \subsubsection{While loop}
We give the semantics of the \texttt{while} loop by unrolling.
Note that the unrolling takes place only when the loop statement
reaches the top of the computation cell; otherwise the unrolling
process may not terminate.  Recall that \K is a rewriting
framework, so one needs to structurally inhibit the application of
rewrite rules; this is in contrast to structural operational semantics
(SOS), where one needs to explicitly give permission (through
conditional rules) to reductions inside constructs' arguments.  Also
note that we preferred to make the rule below structural. */

  rule [while]:
    <k> while B do S => if B then (S ; while B do S) else skip ...</k>
    [:structural:]

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
    if notBool(X in keys(Rho))
  rule [program2-no-vars]: <k> var .Ids; S => S </k>    [:structural:]
end module
