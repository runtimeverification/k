// Copyright (c) 2012-2015 K Team. All Rights Reserved.
require "modules/substitution.k"

/*@
\section{Introductory notes}

Our generic substitution currently expects binding constructs to contain
precisely two arguments, first being an id which is to be bound in the second.
To signal that a construct is a binding one needs to add this attribute
to the syntax declaration.

The running configuration must contain the $\mall{white}{k}{}$ cell,
holding the computation, i.e., the $\lambda$-expression to be evaluated.

We also need to specify that Values are to be treated as finished computations,
or results.
We do so by including them in the KResult category.
*/

module LAMBDA-SYNTAX

  syntax Exp ::= "(" Exp ")"        [bracket]
               | Exp Exp            [seqstrict, left]
               > Val

  syntax Val ::= Id
               > "lambda" Id "." Exp [binder, latex(\lambda{#1}.{#2})]
endmodule

module LAMBDA
 imports LAMBDA-SYNTAX
 imports SUBSTITUTION

 syntax KResult ::= Val

//@ $\beta$-substitution
  rule (lambda X:Id . E:Exp) V:Val => E[V / X]
endmodule
