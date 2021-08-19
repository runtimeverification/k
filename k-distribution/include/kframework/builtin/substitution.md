---
copyright: Copyright (c) 2015-2020 K Team. All Rights Reserved.
---

Capture-Aware Substitution in K
===============================

One of the traditional ways in which functional languages are given operational
semantics is via substitution. In particular, you can view a function as
declaring a particular bound variable, the parameter of the function, as well
as the body of the function, within which both bound and free variables can
occur, and implement the process of beta-reduction (one of the axioms of the
lambda calculus) by means of a substitution operator which is aware of the
difference between free variables and bound variables and prevents variable
capture.

In K this is implemented using two mechanisms: The `KVar` sort, and the
`binder` attribute.

The `KVar` Sort
---------------

K introduces a new hooked sort, `KVar`, which the substitution operator
(defined below) understands in a particular way. The syntax of `KVar` is the
same as for sort `Id` in `DOMAINS`, but with a different sort name. Similarly,
some of the same operators are defined over `KVar` which are defined for `Id`,
such as conversion from `String` to `KVar` and support for the `!Var:KVar`
syntax.

A `KVar` is simply an identifier with special meaning during substitution.
`KVar`s must begin with a letter or underscore,
and can be followed by zero or more letters, numbers, or underscores.

```k
module KVAR-SYNTAX-PROGRAM-PARSING
  imports BUILTIN-ID-TOKENS

  syntax KVar ::= r"(?<![A-Za-z0-9\\_])[A-Za-z\\_][A-Za-z0-9\\_]*"     [prec(1), token]
                | #LowerId                                             [token]
                | #UpperId                                             [token]
endmodule

module KVAR-SYNTAX
  syntax KVar [token, hook(KVAR.KVar)]
endmodule

module KVAR-COMMON
  imports KVAR-SYNTAX
  imports private STRING

  syntax KVar ::= String2KVar (String) [function, functional, hook(STRING.string2token)]
  syntax KVar ::= freshKVar(Int)    [freshGenerator, function, functional, private]

  rule freshKVar(I:Int) => String2KVar("_" +String Int2String(I))
endmodule

module KVAR-SYMBOLIC [symbolic, kast]
  imports KVAR-COMMON
  imports private STRING

  syntax KItem  ::= "#parseToken"  "(" String "," String ")"  [function, klabel(#parseKVar), hook(STRING.parseToken)]
  rule String2KVar(S:String) => {#parseToken("KVar", S)}:>KVar
endmodule

module KVAR
  imports KVAR-COMMON
  imports KVAR-SYMBOLIC
endmodule
```

The `binder` Attribute
----------------------

A production can be given the attribute `binder`. Such a production must have
at least two nonterminals. The first nonterminal from left to right must be of
sort `KVar`, and contains the bound variable. The last nonterminal from left
to right contains the term that is bound. For example, I could describe lambdas
in the lambda calculus with the production 
`syntax Val ::= "lambda" KVar "." Exp [binder]`.

Substitution
------------

K provides a hooked implementation of substitution, currently only implemented
on the Java and LLVM backends. Two variants exist: the first substitutes
a single `KVar` for a single `KItem`. The second takes a `Map` with `KVar`
keys and `KItem` values, and substitutes each element in the map atomically.

Internally, this is implemented in the LLVM backend by a combination of
`de Bruijn` indices for bound variables and names for free variables. Free
variables are also sometimes given a unique numeric identifier in order to
prevent capture, and the rewriter will automatically assign unique names to
such identifiers when rewriting finishes. The names assigned will always begin
with the original name of the variable and be followed by a unique integer
suffix. However, the names assigned after rewriting finishes might be different
from the names that would be assigned if rewriting were to halt prematurely,
for example due to `krun --depth`.

```k
module SUBSTITUTION
  imports private MAP
  imports KVAR

  syntax {Sort} Sort ::= Sort "[" KItem "/" KItem "]"  [function, hook(SUBSTITUTION.substOne), impure]
  syntax {Sort} Sort ::= Sort "[" Map "]"      [function, hook(SUBSTITUTION.substMany), impure]
endmodule
```
