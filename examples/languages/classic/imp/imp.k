module IMP-SYNTAX
/*@ \section{Syntax}
The following constructs are given the expected strictnesses, except for
\textsf{and}, which is only strict in its first argument, because we will
give it a short-circuited semantics (its second argument will only be
evaluated when the first evaluates to true). */

  syntax AExp ::= #Id | #Int
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
  syntax Pgm ::= "var" Ids ";" Stmt      [:prec(110):]
  syntax Ids ::= List{#Id,","}
end module

module IMP
  imports IMP-SYNTAX
/*@ \section{Semantics}
This module defines the semantics of IMP.  We first define
its configuration, then its results, and then its semantic rules. */

/*@ \subsection{Configuration}
The configuration of IMP is trivial: it only contains two cells, one
for the computation and another for the state.  For good encapsulation
and clarity, we place the two cells inside another cell, the ``top'' cell
which is labeled $\top$.  The configuration variable {\em $\PGM} tells
the \K tool where to place the program after parsing.  The ``$\kdot$''
in the \textsf{state} cell is \K's way to say ``nothing''.
Technically, it is a constant which is the unit (or identity) of all
the list, set, multiset, etc., structures in \K.  */

  configuration <T color="yellow">
                  <k color="green"> $PGM:Pgm </k>
                  <state color="red"> .Map </state>
// Replace the above with the following when you want to pass an initial
// state through krun; see commented example programs/sumPgm-novars.imp.
//                  <state color="red"> $STATE:Map </state>
                </T>

/*@ \subsection{Values and results}
IMP only has two types of values: integers and Booleans. */

  syntax Val ::= #Int | #Bool

/*@ Although unnecessary here, it is insightful and useful to
understand the relationship between your language's values and other
syntactic categories.  It is often the case that values form a
subset of the existing language syntax, but sometimes that is not
immediately obvious and sometimes even not true by default (for
example, when defining functional languages we may add closures as
values, even though closures were not expressions in the original
language).  To ease giving the semantics, you typically want to add the
values to your language syntax.  In our case here, you can easily
notice that the IMP values as defined above form a subset of IMP
expressions.  We explicitly say it so anyway below, for clarity. */

  syntax AExp ::= Val

/*@ We have to tell \K that it should interpret values as results of
computations (note that this is not automatic, since sometimes other
syntactic categories are results; e.g., types when defining a type
system).  In this case, since IMP is so simple, we could have also
directly said that integers and Booleans are \K results, without
declaring the syntactic category \textit{Val}.  In general, it is good
practice to add the values of your language as a separate syntactic
category and then instruct the \K tool that those are the results of
your computations.  The main reason for doing so is that the values of
your language will stay the same no matter what semantic style you choose
(thus you make your definition more generic and less dependent on \K). */

  syntax KResult ::= Val

/*@ \subsection{Arithmetic expressions}
The \K semantics of each arithmetic construct is defined below.
We need to do nothing for those arithmetic expression constructs which
are already values, namely for integers and Booleans, because they are
already evaluated. */

/*@ \subsubsection{Variable lookup}
A program variable $X$ is looked up in the state by matching a binding
of the form $X \mapsto I$ in the state cell.  If such a binding does not
exist, then the rewriting process will get stuck.  Thus our semantics of
IMP disallows uses of uninitialized variables. */

  rule <k> X:#Id => I ...</k> <state>... X |-> I ...</state>

/*@ \subsubsection{Arithmetic operators}
There is nothing special about these, except that the rule for division
has a side condition. */

  rule I1:#Int + I2:#Int => I1 +Int I2
  rule I1 / I2 => I1 /Int I2  if I2 =/=Bool 0 

/*@ \subsection{Boolean expressions}
The rules below are straightforward.  Note the short-circuited semantics
of \textsf{and}; this is the reason we annotated the syntax of
\textsf{and} with the \K attribute "strict(1)" instead of "strict". */

  rule I1 <= I2 => I1 <=Int I2
  rule not(T:#Bool) => notBool T  
  rule true and B:BExp => B  
  rule false and _ => false

/*@ \subsection{Statements}
There is one rule per statement construct except for the conditional,
which needs two rules. */

/*@ \subsubsection{Skip}
The \texttt{skip} is simply dissolved.  You can make this rule
structural if you do not want it to count as a computational step. */

  rule skip => .

/*@ \subsubsection{Assignment}
The assigned variable is updated in the state.  The variable is expected
to be declared, otherwise the semantics will get stuck.  At the same time,
the assignment is dissolved. */

  rule <k> X:=I:#Int => . ...</k> <state>... X |-> (_ => I) ...</state>

/*@ \subsubsection{Sequential composition}
Sequential composition is simply dissolved into the \K's builtin
task sequentialization operation.  You can make this rule computational
(i.e., not structural) if you want it to count as a computational step. */

  rule S1:Stmt ; S2:Stmt => S1 ~> S2 [:structural:]

/*@ \subsubsection{Conditional}
The conditional statement has two semantic cases, corresponding to
when its condition evaluates to \texttt{true} or to \texttt{false}. */

  rule if true then S:Stmt else _ => S
  rule if false then _ else S => S

/*@ \subsubsection{While loop}
We give the semantics of the \texttt{while} loop by unrolling.
Note that the unrolling takes place only when the loop statement
reaches the top of the computation cell; otherwise the unrolling
process may not terminate.  Recall that \K is a rewriting
framework, so one needs to structurally inhibit the application of
rewrite rules; this is in contrast to structural operational semantics
(SOS), where one needs to explicitly give permission (through
conditional rules) to reductions inside constructs' arguments.  Also
note that we preferred to make the rule below structural.  If you want
this unrolling step to count as a computational step (though we beg
you to reconsider) then you can remove the ``structural'' tag.  */

  rule <k> while B do S
        => if B then (S ; while B do S) else skip ...</k>  [:structural:]

/*@ \subsection{Programs}
The semantics of an IMP program is that its body statement is executed
in a state initializing all its global variables to 0.  Since \K's
syntactic lists are internally interpreted as cons-lists (i.e., lists
constructed with a head element followed by a tail list), we need to
distinguish two cases, one when the list is empty and another when the
list has at least one element.  We prefer to make the first rule
structural, thinking of dissolving the residual empty \texttt{var}
declaration as a structural cleanup rather than as a computational step. */

  rule <k> var ; S => S ...</k>    [:structural:]
  rule <k> var (X,Xs:Ids => Xs); _ ...</k>
       <state>... . => X |-> 0 ...</state>
end module
