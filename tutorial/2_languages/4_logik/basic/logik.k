// Copyright (c) 2012-2014 K Team. All Rights Reserved.
require "modules/unification.k"

/*!
\title{LOGIK}
\author{Grigore Ro\c{s}u and Traian Florin \c{S}erb\u{a}nu\c{t}\u{a}
        (\texttt{\{grosu,tserban2\}@illinois.edu})}
\organization{University of Illinois at Urbana-Champaign}
*/

/*@ \section{Abstract}

This is the \K semantic definition of LOGIK, a trivial language
capturing the essence of the logic programming paradigm.  In this
definition, we explicitly focus on simplicity and mathematical
clarity, not on advanced logic programming features or performance.
Those are covered in the LOGIK++ extension under
\texttt{examples/logik++}.

Specifically, a LOGIK program consists of a sequence of {\em Horn clauses}
of the form
\begin{quote}
\texttt{P :- P1, P2, ..., Pn .}
\end{quote}
followed by a {\em query} of the form
\begin{quote}
\texttt{?- Q1, Q2, ..., Qm .}
\end{quote}
where \texttt{P}, {\tt P1}, {\tt P2}, ..., {\tt Pn}, {\tt Q1}, {\tt Q2},
..., {\tt Qm} are {\em literals}.  The
symbol ``\texttt{:-}'' is read ``if''.  A literal has the form
\texttt{p(T1,T2,...,Tk)}, where \texttt{p} is a {\em predicate symbol}
and where \texttt{T1,T2,...,Tk} are {\em terms}.  Terms are built as
usual, with {\em operation symbols} and {\em variables}.  A common
convention in logic programming languages, also adopted here, is that
variables are capitalized and operation symbols are not.  Operations
with zero arguments are called {\em constants} and are written without
parentheses, that is, \texttt{c} instead of \texttt{c()}.  Horn
clauses without conditions, called {\em facts}, are written
without ``\texttt{:-}'', that is, ``\texttt{P.}'' instead of
``\texttt{P :- .}''.

For example, the LOGIK program below gives a few facts about a
\texttt{parent} predicate, then several clauses defining some useful
predicates including an \texttt{ancestor} predicate, and finally a
query asking for those who both have ancestors and are ancestors
themselves in the \texttt{parent} relation:

\begin{quote}
\begin{verbatim}
parent(david,john).
parent(jim,david).
parent(steve,jim).
parent(nathan,steve).

grandparent(A,B):-
  parent(A,X),
  parent(X,B).

ancestor(A,B):-
  parent(A,X),
  parents(X,B).

parents(X,X).
parents(A,B):-
  ancestor(A,B).

both(X) :- ancestor(A,X), ancestor(X,B).

?- both(X).
\end{verbatim}
\end{quote}

\noindent
Above, we only have constant operation symbols, so these and variables
are the only terms that can be used in predicates.  As expected, the
LOGIK program above will give us three solutions for \texttt{X}:
\texttt{david}, \texttt{steve}, and \texttt{jim}.  If we inline the
\texttt{both(X)} predicate in the query, that is, if we replace the
query with ``\texttt{?- ancestor(A,X), ancestor(X,B).}'' then we get
10 solutions, one for for each triple \texttt{A}, \texttt{X}, and
\texttt{B} satisfying both predicates \texttt{ancestor(A,X)} and
\texttt{ancestor(X,B)}.

As another example, the program below defines an \texttt{append}
predicate followed by a simple goal:

\begin{quote}
\begin{verbatim}
append(nil,L,L).
append(cons(H,T),L,cons(H,Z)) :- append(T,L,Z).

?- append(cons(a,nil), cons(b,nil), V).
\end{verbatim}
\end{quote}

\noindent
Besides the predicate symbol \texttt{append}, the program above also
includes a constant symbol \texttt{nil} and a binary operation symbol
\texttt{cons}.  Additionally, the query also includes two more
constants, \texttt{a} and \texttt{b}.  The capitalized identifiers are
all variables.  As expected, the LOGIK program above yields only one
solution, namely \texttt{V = cons(a,cons(b,nil))}.  On the other hand,
if we change the query to:

\begin{quote}
\begin{verbatim}
?- append(L1, cons(a,L2), cons(a,cons(b,cons(a,nil)))).
\end{verbatim}
\end{quote}

\noindent
then LOGIK yields two solutions: one where \texttt{L1} is
\texttt{cons(a,cons(b,nil))} and \texttt{L2} is \texttt{nil},
and another where \texttt{L1} is \texttt{nil} and \texttt{L2} is
\texttt{cons(a,cons(b,nil))}.

The programs above all generated {\em ground solutions}, that is,
solutions where the query variables are mapped to ground terms (i.e.,
terms without variables).  Let us now consider the following query:

\begin{quote}
\begin{verbatim}
?- append(cons(a,nil), Y, Z).
\end{verbatim}
\end{quote}

\noindent
There are obviously infinitely many ground solutions for the query
above, e.g.,
\texttt{Y = nil} and \texttt{Z = cons(a,nil)},
\texttt{Y = cons(a,nil)} and \texttt{Z = cons(a,cons(a,nil))},
\texttt{Y = cons(b,nil)} and \texttt{Z = cons(a,cons(b,nil))},
\texttt{Y = cons(c,cons(b,nil))} and \texttt{Z = cons(a,cons(c,cons(b,nil)))},
etc.  However, all the ground solutions for the query above can be
elegantly characterized by the property that \texttt{Z} is bound to a list
starting with \texttt{a} and followed by the list that \texttt{Y} is
bound to.  This property can in fact be described as a {\em symbolic solution}
to the query: \texttt{Z = cons(a,Y)} or, equivalently,
\texttt{Y = Symb} and \texttt{Z = cons(a,Symb)}.  It is possible to
define a ``more general than'' relation on such symbolic solutions,
in the sense that the more particular solution can be obtained as a
specialization/substitution of the more general one, and then it can
be shown that the above is the {\em most general solution} to the
stated query.  Logic programming languages, including our LOGIK,
attempt to always compute such most general solutions.

Logic programming languages are highly non-deterministic, in that
several Horn clauses may be used at the same time, each possibly
resulting in a different solution.  Implementations of logic
programming languages consist of complex, optimized search and
indexing algorithms, which we are not concerned with here.  Instead,
we here take advantage of \K's builtin support for search.
Specifically, to find all the solutions of a LOGIK program, we have to
use \texttt{krun} with the option \texttt{--search}.  However, note
that some programs have infinitely many solutions which cannot relate
to each other by the ``more general'' relation.  For example, the query

\begin{quote}
\begin{verbatim}
?- append(L1, cons(a,L2), L3) .
\end{verbatim}
\end{quote}

\noindent
To address such cases and terminate, logic programming languages allow
the user to choose how many solutions to be computed and displayed.
In LOGIK, we can use the \texttt{--bound} option of \texttt{krun} for
this purpose.

Finally, note that some queries have no solution.  In some cases that
is easy to detect by exhaustive analysis, such as for the following
query:

\begin{quote}
\begin{verbatim}
?- append(cons(a,L1), L2, cons(b,L3)).
\end{verbatim}
\end{quote}

\noindent
Logic programming languages, including LOGIK, terminate in such cases
and report a no solution answer.  However, there are cases where
exhaustive analysis is not sufficient, such as for the query:

\begin{quote}
\begin{verbatim}
?- append(cons(a,L), nil, L).
\end{verbatim}
\end{quote}

\noindent
In such cases, logic programming languages do not terminate.  While
one may devise techniques to detect non-termination in some cases,
one cannot do it in general (same like for all Turing-complete
languages).  */

module LOGIK
  imports UNIFICATION

/*@ Unification is at the core of logic programming.  Here we are
going to use the predefined unification procedure (the same one we
used in the type inferencers in Tutorial 5. */

/*@ \section{Syntax}

The syntax of LOGIK is straightforward: a program is a sequence of
Horn clauses followed by a query: */

  syntax Term ::= Variable
                | Literal                           [klabel('LiteralAsTerm)]
                | Literal "(" Terms ")"
  syntax Terms ::= List{Term,","}
  syntax Clause ::= Term ":-" Terms "." | Term "."
  syntax Query ::= "?-" Terms "."
  syntax Pgm ::= Query | Clause Pgm



/*@ Variables and literals are defined as tokens following the conventions
used in Prolog (variables start with \_ or capital letter, while literals
start with lower case letters): */


  syntax Variable ::= Token{[\_A-Z][a-zA-Z0-9\_]*}               [onlyLabel]
  syntax Literal ::= Token{[a-z][a-zA-Z0-9\_]*}                  [onlyLabel]



/*@ \subsection{Normalizing the definition}

The following simple macros ensure that all clauses will have both a
conclusion and a condition, and that all predicate and operation
symbols take a (potentially empty) list of arguments.  These will
simply the semantics later on, by not having to treat special cases. */

  rule L. => L :- .Terms .                                       [macro]
  rule 'LiteralAsTerm(X:Literal) => X(.Terms)                    [macro]

/*@ \section{Configuration}

The configuration stores each clause in its own cell for easy access,
and the most general unifier in a cell named \textsf{mgu}, same like
the type inferencers.  The \textsf{k} cell holds the query and the
\textsf{fresh} cell holds a fresh clause instance to be attempted on
the next query item.  To more easily read the solutions, we add a
second top-level cell, \textsf{solution}.  Both top cells are
optional.  Indeed, we start with the main top cell and, when a
solution is found, we move it into the \textsf{solution} cell and
discard the main cell. */

  configuration <T color="yellow" multiplicity="?">
                  <k color="green"> $PGM:Pgm </k>
                  <fresh color="orange"> .K </fresh>
                  <mgu color="blue"> (.Mgu)::MguOrError </mgu>
                  <br/>
                  <clauses color="red">
                    <clause color="pink" multiplicity="*"> .K </clause>
                  </clauses>
                </T>
                <solution multiplicity="?"> .Map </solution>

/*@ \section{Pre- and post-processing}

Before we launch the semantics, we first scan the given program and
place each clause in its own cell, and then place the query in the
\textsf{k} cell, creating the solution cell, too: */

  rule <k> C:Clause Pgm => Pgm </k>
       (. => <clause> C </clause>)

  rule <k> ?- Ls:Terms. => Ls ...</k>
       (. => <solution> #metaVariablesMap(Ls) </solution>)

//@ We also sequentialize the goals for easier processing:
  rule L:Term, Ls:Terms => L ~> Ls
  rule .Terms => .

/*@ When all the goals are solved, indicated by the empty \textsf{k}
cell, the calculated most general unifier (mgu) is in the \textsf{mgu}
cell.  In that case, to ease reading of the final solution we apply
the mgu to the solution map and delete the rest of the configuration: */

  rule (<T>... <k> . </k> <mgu> Theta:Mgu </mgu> ...</T> => .)
       <solution> Solution:Map => applyMgu(Theta,Solution) </solution>

/*@ Since we are not interested in seeing the failed attempts to solve
the query, we collapse all the error configurations into an empty
configuration (recall that both top-level cells in the configuration
were declared optional).  This way, if we see an empty configuration
when we search for all solutions, we know that some attempts failed
(but we do not know which ones). */

  rule <T>... <mgu> _:MguError </mgu> ...</T> <solution> _ </solution> => .

/*@ \section{Semantics}

Once all the infrastructure is in place, the actual semantics of LOGIK
is quite simple.  All we have to do is to pick some (fresh instance of
a) clause, then unify its conclusion with the first query literal, and
then replace that literal with condition of the clause.  The intuition
here is the following: to satisfy the first literal in the query, we
need to find some instance of some clause that matches it, and then to
similarly show that we can satisfy the conditions of that clause.
Mathematically, this is an instance of the proof principle called
{\em resolution}: if $p \vee q$ and $\neg p \vee r$ hold, then so does
$q \vee r$.  We let it as an exercise to the reader to see how the two
relate (hint: assume the negation of the goal together with all the
clauses, and then derive {\em false}). */


/*@ The following two rules are tightly connected and they together
perform the following core task: pick a fresh instance of a clause
which unifies with the first goal item, then add its conditions as new
goals.  By a ``fresh instance'' of a clause we mean one whose
variables are renamed with fresh names; we need that in order to avoid
undesired unification conflicts due to particular names chosen for
variables in the original program, as well as conflicts due to
subsequent uses of the same clause.  It is safe to rename the
variables in a clause, because clauses are universally quantified in
their variables.  This process of creating a fresh instance of a
clause is similar to how we created fresh instances of type schemas in
the higher-order type inferencer discussed in Tutorial 5.  Indeed, we
can safely regard clauses as ``clause schemas'' comprising infinitely
many instances, one for each context. */

/*@ Pick a clause and generate a fresh instance of it when the
\textsf{fresh} cell is empty: */

  rule <fresh> . => renameVariables(C) </fresh>  <clause> C </clause>
    [transition]

/*@ Unify the goal with the fresh clause's head, replace the goal
with the clause body, and empty the \textsf{fresh} cell (so that
another clause can be chosen using the rule above):  */

  rule <k> L':Term => Ls ...</k>
       <fresh>  L:Term :- Ls:Terms. => . </fresh>
       <mgu> Theta:Mgu => updateMgu(Theta,L,L') </mgu>

/*@ Note that there is no problem if a clause is chosen whose
conclusion literal does not unify with the first goal literal.  In
this case the mgu update operation fails, so the post-processing rule
above dissolves the configuration in an empty one.  The search
option of \texttt{krun} will systematically try all clauses, so no
solution is missed.  Of course, the above is not the most efficient
way to implement a logic programming language, but recall that our
objective here was to present a simple and mathematically clean
solution.  We encourage the interested reader to consult the LOGIK++
language definition for a more efficient definition of a richer logic
programming language. */
endmodule
