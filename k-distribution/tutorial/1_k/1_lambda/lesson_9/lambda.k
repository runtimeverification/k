// Copyright (c) 2014-2019 K Team. All Rights Reserved.

// C/Java-like comments like this one are completely ignored by the K tool.
/* These ones, which may spread over
several lines, are ignored, too.  */

// Use the "@" symbol right after // or /* in order for the comment to be
// considered an annotation and thus be processed by the K tool when it
// generates documentation.

// Use the "!" symbol right after // or /* if you want the comment to be
// considered a header annotation, that is, one which goes into the header
// of the generated Latex documentation, that is, before "\begin{document}"
// (e.g., when your comment includes macros, or defines a title, etc.)

/*!
\setlength{\parindent}{1em}
\title{Tutorial 1 --- LAMBDA}
\author {Grigore Ro\c{s}u (\texttt{grosu@illinois.edu})}
\organization{University of Illinois at Urbana-Champaign}
*/

/*@ \section{Abstract}
This file defines a simple functional language in \K, called LAMBDA,
using a substitution style.  The explicit objective here is to teach some
\K concepts and how they work in the K tool, and not to teach
$\lambda$-calculus or to argue for one definitional style against another
(e.g., some may prefer environment/closure-based definitions of such
languages).

Note that the subsequent definition is so simple, that it hardly shows any
of the strengths of \K.  Perhaps the most interesting \K aspect it shows is
that substitution can be defined fully generically, and then used to give
semantics to various constructs in various languages.

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
*/

/*@ \section{Substitution}
We need the predefined substitution module, so we require it with the command
below.  Then we should make sure that we import its module called SUBSTITUTION
in our LAMBDA module below. */

require "substitution.k"

module LAMBDA
  imports DOMAINS
  imports SUBSTITUTION

/*@ \section{Basic Call-by-value $\lambda$-Calculus}

We first define a conventional call-by-value $\lambda$-calculus, making sure
that we declare the lambda abstraction construct to be a binder, the
lambda application to be strict, and the parentheses used for grouping as
a bracket. */

/*@ \paragraph{Note:}{
Syntax in \K is defined using the familiar BNF notation, with
terminals enclosed in quotes and nonterminals starting with capital
letters.  \K actually extends BNF with several attributes, which will be
described in this tutorial.
} */

/*@ \paragraph{Note:}{
The \texttt{strict} constructs can evaluate their arguments in any (fully
interleaved) order.
} */

//@ The initial syntax of our $\lambda$-calculus:

  syntax Val ::= KVar
               | "lambda" KVar "." Exp  [binder, latex(\lambda{#1}.{#2})]
  syntax Exp ::= Val
               | Exp Exp              [left, strict]
               | "(" Exp ")"          [bracket]
  syntax KResult ::= Val

//@ \section{$\beta$-reduction}

  rule (lambda X:KVar . E:Exp) V:Val => E[V / X]

/*@ \section{Integer and Boolean Builtins}
The LAMBDA arithmetic and Boolean expression constructs are simply rewritten
to their builtin counterparts once their arguments are evaluated.
The operations with subscripts in the right-hand sides of the rules below are
builtin and come with the corresponding builtin sort; they are actually
written like \texttt{+Int} in ASCII, but they have \LaTeX\ attributes to be
displayed like $+_{\it Int}$ in the generated document.  Note that the
variables appearing in these rules have integer sort.  That means that these
rules will only be applied after the arguments of the arithmetic constructs
are fully evaluated to \K results; this will happen thanks to their strictness
attributes declared as annotations to their syntax declarations (below).  */

  syntax Val ::= Int | Bool
  syntax Exp ::= Exp "*" Exp          [strict, left]
               | Exp "/" Exp          [strict]
               > Exp "+" Exp          [strict, left]
               > Exp "<=" Exp         [strict]
  rule I1 * I2 => I1 *Int I2
  rule I1 / I2 => I1 /Int I2  requires I2 =/=Int 0
  rule I1 + I2 => I1 +Int I2
  rule I1 <= I2 => I1 <=Int I2

/*@ \section{Conditional}
Note that the \texttt{if} construct is strict only in its first argument. */

  syntax Exp ::= "if" Exp "then" Exp "else" Exp    [strict(1)]
  rule if true  then E else _ => E
  rule if false then _ else E => E

/*@ \section{Let Binder}
The let binder is a derived construct, because it can be defined using
$\lambda$. */

  syntax Exp ::= "let" KVar "=" Exp "in" Exp
  rule let X = E in E':Exp => (lambda X . E') E                         [macro]

/*@ \section{Letrec Binder}
We prefer a definition based on the $\mu$ construct.  Note that $\mu$ is not
really necessary, but it makes the definition of letrec easier to understand
and faster to execute. */

  syntax Exp ::= "letrec" KVar KVar "=" Exp "in" Exp
               | "mu" KVar "." Exp                  [binder, latex(\mu{#1}.{#2})]
  rule letrec F:KVar X:KVar = E in E' => let F = mu F . lambda X . E in E' [macro]
  rule mu X . E => E[(mu X . E) / X]
endmodule
