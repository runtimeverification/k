require /modules/substitution

module EXP-UNTYPED-SUBSTITUTION-SYNTAX

/*@ \section{Syntax}
EXP is an expression language, so it has only one syntactic category,
\textit{Exp}.  The syntax of EXP consists of conventional arithmetic
constructs and conventional higher-order functional constructs.  All
these constructs are very basic and simple, pushed to the essence of
the notion that they are attempting to capture. */

/*@ \subsection{Arithmetic constructs}
These are similar to those in imperative and object oriented
languages (for example see IMP) but note that in this
substitution-based definition of EXP we prefer to make explicit a
subcategory of \textit{Exp} values here in the syntax (in other
definitions, particularly in environment-based ones, we introduce
values as part of the semantics).  Note that identifiers are values.
$\lambda$-abstractions will also be defined as values shortly. */

  syntax Val ::= #Int | #Bool | #Id
  syntax Exp ::= Val 
               | Exp "+" Exp                [:strict prec 33 gather(E e):]
               | Exp "-" Exp                [:strict prec 33 gather(E e):]
               | Exp "*" Exp                [:strict prec 31 gather(E e):]
               | Exp "/" Exp                [:strict prec 31 gather(E e):]
               | Exp "%" Exp                [:strict prec 31 gather(E e):]
               | "-" Exp                    [:strict:]
               | Exp "<" Exp                [:strict prec 37:]
               | Exp "<=" Exp               [:strict prec 37:]
               | Exp ">" Exp                [:strict prec 37:]
               | Exp ">=" Exp               [:strict prec 37:]
               | Exp "==" Exp               [:strict prec 37:]
               | Exp "!=" Exp               [:strict prec 37:]
               | Exp "and" Exp              [:strict prec 55 gather(E e):]
               | Exp "or" Exp               [:strict prec 59 gather(E e):]
               | "not" Exp                  [:strict prec 53:]

/*@ \subsection{Functional constructs}
The constructs below are well-known: \texttt{lambda} and concatenation
of expressions are the function abstraction and application,
\texttt{if} is the conditional construct which here can take any
expressions as branches, \texttt{mu} is the usual recursive binder,
and \texttt{let} and \texttt{letrec} are the usual functional derived
constructs which can be desugared as shown in the two macros below.
The {\color{blue}binder} annotation for the $\lambda$ and $\mu$ constructs
tells our generic substitution (defined in module
\texttt{SUBSTITUTION}, which is imported in the semantic module below)
that these constructs bind their first argument in the second and thus
are subject to $\alpha$-conversion (to avoid variable-capture).  Note
that the \texttt{lambda} construct yields a value, while the
\texttt{mu} construct does not.  Also, note that application is strict
in both arguments, to capture the fact that EXP is call-by-value. */

  syntax Val ::= "lambda" #Id "." Exp       [:binder latex "\lambda{#1}.{#2}":]
  syntax Exp ::= "if" Exp "then" Exp "else" Exp [:strict(1):]
               | Exp Exp                    [:strict prec 10 gather(E e):]
               | "mu" #Id "." Exp           [:binder latex "\mu{#1}.{#2}":]
               | "let" #Id "=" Exp "in" Exp
               | "letrec" #Id #Id "=" Exp in Exp

/*@ \subsection{Desugaring macros}
The desugaring rules below are standard, although note that we do not
want to apply them when we do type inference (because we want our type
inferencer to be {\em let} polymorphic). */

  macro let X:#Id = E:Exp in E':Exp = (lambda X . E') E
  macro (letrec F:#Id X = E in E') = (let F = mu F . (lambda X . E) in E')

end module


module EXP-UNTYPED-SUBSTITUTION
  imports EXP-UNTYPED-SUBSTITUTION-SYNTAX + SUBSTITUTION

/*@ \section{Semantics}
Since our \K definition here is substitution-based, there is no need to
lookup variables (variables are simply substituted when needed) and no
need to give a semantics to $\lambda$-abstractions (they are simply
applied via the $\beta$-reduction rule). */

/*@ \subsection{Values and results}
We have to tell the \K tool that values should be regarded as results
of computations. */

  syntax KResult ::= Val

/*@ \subsection{Configuration}
The one-cell configuration below is standard for simple
substitution-based semantics. */

  configuration <k color="green"> $PGM:Exp </k>
  
  // termination rule; useful for making sure program finished.  
  // Can be removed when we have better krun tools for displaying final config
  rule <k> V:Val </k> (<nextId> _:K </nextId> => .)

/*@ \subsection{Arithmetic constructs}
The block of rules below are taken over, unchanged, from the semantics
of IMP\@.  The rules for equality test need to be restricted to only
apply in context, so they were given separate semantics underneath. */

  rule I1:#Int + I2:#Int => I1 +Int I2
  rule _-_(I1,I2) => _-Int_(I1,I2)
  rule I1 * I2 => I1 *Int I2
  rule I1 / I2 => I1 /Int I2 when I2 =/=Bool 0
  rule I1 % I2 => I1 %Int I2 when I2 =/=Bool 0
  rule - I:#Int => -Int I
  rule I1 < I2 => I1 <Int I2
  rule I1 <= I2 => I1 <=Int I2
  rule I1 > I2 => I1 >Int I2
  rule I1 >= I2 => I1 >=Int I2
  rule T1:#Bool and T2:#Bool => T1 andBool T2
  rule T1 or T2 => T1 orBool T2
  rule not(T:#Bool) => notBool(T)

/*@ \subsection{Equality test}
In this substitution-based definition we need to be careful when
defining equality, as ids are also values.  To be safe, we restrict
the semantics of equality only to redex positions, i.e., at the top of
the \textsf{k} cell. */

  rule <k> V1:Val == V2:Val => V1 ==Bool V2 ...</k>
  rule <k> V1 != V2 => V1 =/=Bool V2 ...</k>

/*@ \subsection{Conditional}
The two rules below are straightforward, almost identical to those in
IMP\@.  The only difference is that in EXP the conditional is an
expression, rather than a statement, construct. */

  rule if  true then E else  _  => E
  rule if false then  _  else E => E

/*@ \subsection{$\beta$-reduction and $\mu$-unrolling}

Since our semantics is call-by-value, we only reduce application or
unroll $\mu$ when they are in redex positions, which in \K is
equivalent to being at the top of the \textsf{k} cell. */

  rule <k> (lambda X:#Id . E:Exp) V:Val => E[V/X]  ...</k>

  rule <k> mu X . E => E[(mu X.E) / X] ...</k>

end module
