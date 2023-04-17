---
copyright: Copyright (c) Runtime Verification, Inc. All Rights Reserved.
---

# Lesson 2.1: Macros, Aliases, and Anywhere Rules

The purpose of this lesson is to explain the behavior of the `macro`,
`macro-rec`, `alias`, and `alias-rec` production attributes, as well as the
`anywhere` rule attribute. These attributes control the meaning of how rules
associated with them are applied.

## Macros

Thus far in the K tutorial, we have described three different types of rules:

1. Top-level rewrite rules, which rewrite a configuration composed of cells to
another configuration;
2. Function rules, which define the behavior of a function written over
arbitrary input and output types; and
3. Simplification rules, which describe ways in which the symbolic execution
engine ought to simplify terms containing symbolic values.

This lesson introduces three more types of rules, the first of which are
**macros**. A production is a macro if it has the `macro` attribute, and all
rules whose top symbol on the left hand side is a macro are **macro rules**
which define the behavior of the macro. Like function rules and simplification
rules, macro rules do not participate in cell completion. However, unlike
function rules and simplification rules, macro rules are applied **statically**
before rewriting begins, and the macro symbol is expected to no longer appear
in the initial configuration for rewriting once all macros in that
configuration are rewritten.

The rationale behind macros is they allow you to define one piece of syntax
in terms of another piece of syntax without any runtime overhead associated
with the cost of rewriting one to the other. This process is a common one in
programming language design and specification and is referred to as
**desugaring**; The syntax that is transformed is typically also referred to as
**syntactic sugar** for another type of syntax. For example, in a language with
`if` statements and curly braces, you could write the following fragment
(`lesson-01.k`):

```k
module LESSON-01
  imports BOOL

  syntax Stmt ::= "if" "(" Exp ")" Stmt             [macro]
                | "if" "(" Exp ")" Stmt "else" Stmt
                | "{" Stmts "}"
  syntax Stmts ::= List{Stmt,""}
  syntax Exp ::= Bool

  rule if ( E ) S => if ( E ) S else { .Stmts }
endmodule
```

In this example, we see that an if statement without an `else` clause is
defined in terms of one with an `else` clause. As a result, we would only
need to give a single rule for how to rewrite `if` statements, rather than
two separate rules for two types of `if` statements. This is a common pattern
for dealing with program syntax that contains an optional component to it.

It is worth noting that by default, macros are not applied recursively. To be
more precise, by default a macro that arises as a result of the expansion of
the same macro is not rewritten further. This is primarily to simplify the 
macro expansion process and reduce the risk that improperly defined macros will
lead to non-terminating behavior.

It is possible, however, to tell K to expand a macro recursively. To do this,
simply replace the `macro` attribute with the `macro-rec` attribute. Note that
K does not do any kind of checking to ensure termination here, so it is
important that rules be defined correctly to always terminate, otherwise the
macro expansion phase will run forever. Fortunately, in practice it is very
simple to ensure this property for most of the types of macros that are
typically used in real-world semantics.

### Exercise

Using a `Nat` sort containing the constructors `0` and `S` (i.e., a
[Peano-style](https://en.wikipedia.org/wiki/Peano_axioms) axiomatization of the
natural numbers where `S(N) = N + 1`, `S(S(N)) = N + 2`, etc), write a macro
that will compute the sum of two numbers.

## Aliases

**NOTE**: This lesson introduces the concept of "aliases", which are a variant
of macros. While similar, this is different from the concept of "aliases" in
matching logic, which is introduced in Lesson 2.16.

Macros can be very useful in helping you define a programming language.
However, they can be disruptive while pretty printing a configuration. For
example, you might write a set of macros that transforms the code the user
wrote into equivalent code that is slightly harder to read. This can make it
more difficult to understand the code when it is pretty printed as part of the
output of rewriting.

K defines a relatively straightforward but novel solution to this problem,
which is known as a K **alias**. An alias in K is very similar to a macro,
with the exception that the rewrite rule will also be applied **backwards**
during the pretty-printing process.

It is very simple to make a production be an alias instead of a macro: simply
use the `alias` or `alias-rec` attributes instead of the `macro` or `macro-rec`
attributes. For example, if the example involving `if` statements above was
declared using an alias instead of a macro, the `Stmt` term `if (E) {} else {}`
would be pretty-printed as `if (E) {}`. This is because during pretty-printing,
the term participates in another macro-expansion pass. However, this macro
expansion step will only apply rules with the `alias` or `alias-rec` attribute,
and, critically, it will reverse the rule by treating the left-hand side as if
it were the right-hand side, and vice versa.

This can be very useful to allow you to define one construct in terms of
another while still being able to pretty-print the result as if it were
the original term in question. This can be especially useful for applications
of K where we are taking the output of rewriting and attempting to use it as
a code fragment that we then execute, such as with test generation.

### Exercise

Modify `LESSON-01` above to use an alias instead of a macro and experiment
with how various terms are pretty-printed by invoking `krun` on them.

## `anywhere` rules

The last type of rule introduced in this lesson is the **anywhere rule**. An
anywhere rule is specified by adding the `anywhere` attribute to a rule. Such a
rule is similar to a function rule in that it does not participate in cell
completion, and will apply anywhere that the left-hand-side matches in the
configuration, but distinct in that the symbol in question can still be matched
against in the left-hand side of other rules, even during concrete rewriting.
The reasoning behind this is that instead of the symbol in question being a
constructor, it is a constructor *modulo* the axioms defined with the
`anywhere` attribute. Essentially, the rules with the `anywhere` attribute will
apply as soon as they appear in the right-hand side of a rule being applied,
but the symbol in question will still be treated as a symbol that can be
matched on if it is not completely removed by those rules.

This can be useful in certain cases to allow you to define transformations over
particular pieces of syntax while still generally giving those pieces of syntax
another meaning when the anywhere rule does not apply. For example, the ISO C
standard defines the semantics of `*&x` as exactly equal to `x`, with no
reading or writing of memory taking place, and the K semantics of C implements
this functionality using an anywhere rule that is applied at compilation time.

**NOTE**: the `anywhere` attribute is only implemented on the LLVM backend
currently. Attempting to use it in a semantics that is compiled with the
Haskell backend will result in an error being reported by the compiler. This
should be remembered when using this attribute, as it may not be suitable for
a segment of a semantics which is intended to be symbolically executed.

## Exercises

1. Write a version of the calculator from Lesson 1.14 Exercise 1, which uses
the same syntax for evaluating expressions, but defines its arithmetic logic
using `anywhere` rules rather than top-level rewrite rules.

## Return to Top

[Click here](../README.md) to return to the Table of Contents for Section 2.
