// C/Java-style comments like this one are completely ignored by the K tool.
/* These ones, which may spread over
several lines, are ignored, too */

// Use the "@" symbol right after // or /* in order for the comment to be
// considered an annotations and thus be processed by the K tool when it
// generates documentation.

// Use the "!" symbol right after // or /* if you want the comment to be
// considered a header annotation, that is, one which goes into the header
// of the generated Latex documentation, that is, before "\begin{document}"
// (e.g., when your comment includes macros, or defines a title, etc)

/*!
\setlength{\parindent}{1em}
\title{Tutorial 1 --- LAMBDA}
\author{Grigore Ro\c{s}u (\texttt{grosu@illinois.edu})}
\organization{University of Illinois at Urbana-Champaign}
*/

/*@ \section{Abstract}
This file defines a simple functional language in \K, called LAMBDA,
using a substitution style.  The explicit objective here is to teach some
\K concepts and how they work in the \K tool, and not to teach lambda-calculus
or to argue for one definitional style against another (e.g., some may prefer
environment/closure-based definitions to such languages).

Note that the subsequent definition is so simple, that it hardly shows any
of the strengths of \K.  Perhaps the most interesting \K aspect it shows is
that substitution can be defined fully generically, and then used to give
semantics to various constructs in various languages. */


/*@ \section{Substitution}
We need the predefined substitution module, so we require it with the command
below.  Then we should make sure that we import its module called SUBSTITUTION
in our LAMBDA module below. */

require "modules/substitution.k"

module LAMBDA
  imports SUBSTITUTION

/*@ \section{Basic Call-By-Value $\lambda$-Calculus}

We first define a conventional call-by-value $\lambda$-calculus, making sure
that we declare the lambda abstraction construct to be a binder, the
lambda application to be strict, and the parenthesis used for grouping as
a bracket. */


//@ The initial syntax of our $\lambda$-calculus:

  syntax Val ::= Id
               | "lambda" Id "." Exp  [binder, latex(\lambda{#1}.{#2})]
  syntax Exp ::= Val
               | Exp Exp              [strict, left]
               | "(" Exp ")"          [bracket]
  syntax KResult ::= Val

//@ $\beta$-reduction:

  rule (lambda X:Id . E:Exp) V:Val => E[V / X]

//@ \section{Integer and Boolean Builtins}

  syntax Val ::= Int | Bool
  syntax Exp ::= Exp "*" Exp          [strict, left]
               | Exp "/" Exp          [strict]
               > Exp "+" Exp          [strict, left]
               > Exp "<=" Exp         [strict]
  rule I1:Int * I2:Int => I1 *Int I2
  rule I1:Int / I2:Int => I1 /Int I2
  rule I1:Int + I2:Int => I1 +Int I2
  rule I1:Int <= I2:Int => I1 <=Int I2

//@ \section{Conditional}

  syntax Exp ::= "if" Exp "then" Exp "else" Exp  [strict(1)]
  rule if true  then E else _ => E
  rule if false then _ else E => E

/*@ \section{Let Binder}
The let binder is a derived construct, as it can be defined using $\lambda$. */

  syntax Exp ::= "let" Id "=" Exp "in" Exp
  rule let X = E in E':Exp => (lambda X . E') E
    [structural]

/*@ \section{Letrec Binder}
We prefer a definition based on the $\mu$ construct.  Note that $\mu$ is not
really necessary, but it makes the definition of letrec easier to understand
and faster to execute. */

  syntax Exp ::= "letrec" Id Id "=" Exp "in" Exp
               | "mu" Id "." Exp      [binder, latex(\mu{#1}.{#2})]
  rule letrec F:Id X = E in E' => let F = mu F . lambda X . E in E'
    [structural]
  rule mu X . E => E[(mu X . E) / X]
endmodule
