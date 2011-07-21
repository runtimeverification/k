module IMP-SYNTAX imports #INT + #ID
/*@ The following constructs are given the expected strictnesses, except for
\textsf{and}, which is only strict in its first argument, because we will
give it a short-circuited semantics (its second argument will only be
evaluated when the first evaluates to true). */

  syntax AExp ::= Id | Int
                | AExp + AExp                  [prec 33 gather (E e) strict]
                | AExp / AExp                  [prec 31 gather (E e) strict]
  syntax BExp ::= Bool
                | AExp <= AExp                 [prec 37 strict]
                | not BExp                     [prec 53 strict]
                | BExp and BExp                [prec 55 strict(1)]
  syntax Stmt ::= skip ;
                | Id = AExp ;                  [prec 40 strict(2)]
                | Stmt Stmt                    [prec 60 gather (e E)]
                | if BExp then Stmt else Stmt  [prec 59 strict(1)]
                | while BExp do Stmt           [prec 59]
end module


module IMP-PROGRAMS imports IMP-SYNTAX
  syntax Id   ::= a | b | c | d | e | f | g | h | i | j | k | l | m
                | n | o | p | q | r | s | t | u | v | w | x | y | z
  syntax Stmt ::= sumPgm
                | collatzPgm | collatzStmt
                | multiplicationStmt | primalityStmt | countPrimesPgm

macro sumPgm = (
     n=10;
     s=0;
     while not(n<=0) do (
       s=s+n;
       n=n+-1;
     )
)

macro collatzStmt = (
     while not (n<=1) do (
       s=s+1;
       q=n/2;
       r=q+q+1;
       if r<=n
         then n=n+n+n+1; else n=q;
     )
)

macro collatzPgm = (
   m=5;
   s=0;
   while not(m<=2) do (
     n=m;
     m=m+-1;
     collatzStmt
   )
) 

--- fast multiplication (base 2) algorithm
macro multiplicationStmt = ( 
  z=0;
  while not(x<=0) do (
    q=x/2;
    r=q+q+1;
    if r<=x then z=z+y;
    else skip;
    x=q;
    y=y+y;
  )
) 

macro primalityStmt = (
  i=2;
  q=n/i;
  t=1;
  while (i<=q and 1<=t) do (
    x=i;
    y=q;
    multiplicationStmt 
    if n<=z then t=0; else (
      i=i+1;
      q=n/i;
    )
  )
) 

macro countPrimesPgm = (
   m=10;
   s=0; n=2;
   while n<=m do (
     primalityStmt
     if 1<=t then s=s+1; else skip;
     n=n+1;
   )
)

end module


module IMP-SEMANTICS imports IMP-SYNTAX
/*@ \section*{Semantics}
This module defines the semantics of IMP.  We first define
its configuration, then its results, and then its semantic rules. */

/*@ \subsection*{Configuration}
The configuration of IMP is trivial: it only contains two cells, one
for the computation and another for the state.  For good encapsulation
and clarity, we place the two cells inside another cell, the ``top'' cell
which is labeled $\top$. */

  configuration <T color="yellow">
                  <k color="green"> .K </k>
                  <state color="red"> .Map </state>
                </T>

/*@ \subsection{Results}
IMP only has two types of results: integers and Booleans. */

  syntax KResult ::= Int | Bool

/*@ \subsection{Arithmetic Expressions}
The \K semantics of each arithmetic construct is defined below.
We need to do nothing for integers. */

/*@ \subsubsection{Variable Lookup}
A program variable $X$ is looked up in state $\Large\sigma$ using the
builtin map lookup operation ${\Large\sigma}(X)$.  Note that this
operation requires $\Large\sigma$ to be defined in $X$; otherwise the
rewriting process will get stuck.  This means that our semantics of
IMP disallows uses of uninitialized variables.  Variables are initialized
using the assignment statement whose semantics is defined below. */

  rule <k> X:Id => Sigma(X) <_/k> <state> Sigma:Map </state>

/*@ \subsubsection{Arithmetic operators}
There is nothing special about these, except that the rule for division
has a side condition. */

  rule I1:Int + I2:Int => I1 +Int I2
  rule I1 / I2 => I1 /Int I2  if I2 =/=Bool 0 

/*@ \subsection{Boolean Expressions}
The rules below are straightforward.  Note the short-circuited semantics
of \textsf{and}; this is the reason we annotated the syntax of
\textsf{and} with the \K attribute "strict(1)" instead of "strict". */

  rule I1 <= I2 => I1 <=Int I2
  rule not(T:Bool) => notBool T  
  rule true and B:BExp => B  
  rule false and _ => false

/*@ \subsection{Statements}
There is one rule per statement construct except for the conditional,
which needs two rules. */

/*@ \subsubsection{Skip}
The \texttt{skip} is simply dissolved.  One can make this
rule structural if one does not want it to count as a computational step. */

  rule skip; => .

/*@ \subsubsection{Assignment}
The assigned variable is updated in the state: ${\Large\sigma}[I/X]$
adds the mapping $X \mapsto I$ to $\Large\sigma$ in case $\Large\sigma$
is not defined in $X$, and it changes the current mapping of $X$
(to point to $I$) in case $\Large\sigma$ is defined in $X$.
At the same time, the assignment is dissolved. */

  rule <k> X=I:Int; => . <_/k> <state> Sigma => Sigma[I/X] </state> 

/*@ \subsubsection{Sequential Composition}
Sequential composition is simply dissolved into the \K's builtin
task sequentialization operation.  Like for \texttt{skip}, one is
free to make this rule structural if one does not want it to count
as a computational step.  */

  rule S1:Stmt S2:Stmt => S1~>S2

/*@ \subsubsection{Conditional}
The conditional statement has two semantic cases, corresponding to
when its condition evaluates to \texttt{true} or to \texttt{false}. */

  rule if true then S:Stmt else _ => S
  rule if false then _ else S => S

/*@ \subsubsection{While Loop}
We give the semantics of the \texttt{while} loop by unrolling.
Note that the unrolling takes place only when the loop statement
reaches the top of the computation cell; otherwise the unrolling
process may not terminate.  Recall that \K is a rewriting
framework, so one needs to structurally inhibit the
application of rewrite rules; this is in contrast to structural
operational semantics (SOS), where one needs to explicitly give
permission (through conditional rules) to reductions inside
constructs' arguments.  Also note that we preferred to make the
rule below structural.  If one wants this unrolling step to count
as a computational step (though we beg one to reconsider)
then one can remove the ``structural'' tag.  */

  rule <k> while B do S => if B then (S while B do S) else skip; <_/k> [structural]
end module

module IMP imports IMP-PROGRAMS + IMP-SEMANTICS 
  syntax Bag ::= [[ KLabel ]] [latex "\llbracket\,{#1}\,\rrbracket"]
  macro [[KL:KLabel]] = <T_> <k> KL(.List{K}) </k> <_/T>
end module
