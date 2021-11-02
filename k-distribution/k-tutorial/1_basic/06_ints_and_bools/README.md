# Lesson 1.6: Integers and Booleans

The purpose of this lesson is to explain the two most basic types of builtin
sorts in K, the `Int` sort and the `Bool` sort, representing
**arbitrary-precision integers** and **Boolean algebra**.

## Builtin sorts in K

K provides definitions of some useful sorts in
[domains.md](../../../include/kframework/builtin/domains.md), found in the
`include/kframework/builtin` directory of the K installation. This file is
defined via a
[Literate programming](https://en.wikipedia.org/wiki/Literate_programming)
style that we will discuss in a future lesson. We will not cover all of the 
sorts found there immediately, however, this lesson discusses some of the
details surrounding integers and Booleans, as well as providing information
about how to look up more detailed knowledge about builtin functions in K's
documentation.

## Booleans in K

The most basic builtin sort K provides is the `Bool` sort, representing
Boolean values (i.e., `true` and `false`). You have already seen how we were
able to create this type ourselves using K's parsing and disambiguation
features. However, in the vast majority of cases, we prefer instead to import
the version of Boolean algebra defined by K itself. Most simply, you can do
this by importing the module `BOOL` in your definition. For example
(`lesson-06-a.k`):

```k
module LESSON-06-A
  imports BOOL

  syntax Fruit ::= Blueberry() | Banana()
  syntax Bool ::= isBlue(Fruit) [function]

  rule isBlue(Blueberry()) => true
  rule isBlue(Banana()) => false
endmodule
```

Here we have defined a simple **predicate**, i.e., a function returning a
Boolean value. We are now able to perform the usual Boolean operations of
and, or, and not over these values. For example (`lesson-06-b.k`):"

```k
module LESSON-06-B
  imports BOOL

  syntax Fruit ::= Blueberry() | Banana()
  syntax Bool ::= isBlue(Fruit) [function]

  rule isBlue(Blueberry()) => true
  rule isBlue(Banana()) => false

  syntax Bool ::= isYellow(Fruit) [function]
                | isBlueOrYellow(Fruit) [function]

  rule isYellow(Banana()) => true
  rule isYellow(Blueberry()) => false

  rule isBlueOrYellow(F) => isBlue(F) orBool isYellow(F)
endmodule
```

In the above example, Boolean **inclusive or** is performed via the `orBool`
function, which is defined in the `BOOL` module. As a matter of convention,
many functions over builtin sorts in K are suffixed with the name of the
primary sort over which those functions are defined. This happens so that the
syntax of K does not (generally) conflict with the syntax of any other
programming language, which would make it harder to define that programming
language in K.

### Exercise

Write a function `isBlueAndNotYellow` which computes the appropriate Boolean
expression. If you are unsure what the appropriate syntax is to use, you
can refer to the `BOOL` module in
[domains.md](../../../include/kframework/builtin/domains.md). Add a term of
sort `Fruit` for which `isBlue` and `isYellow` both return true, and test that
the `isBlueAndNotYellow` function behaves as expected on all three `Fruit`s.

### Syntax Modules

For most sorts in `domains.md`, K defines more than one module that can be
imported by users. For example, for the `Bool` sort, K defines the `BOOL`
module that has previously already been discussed, but also provides the
`BOOL-SYNTAX` module. This module, unlike the `BOOL` module, only declares the
values `true` and `false`, but not any of the functions that operate over the
`Bool` sort. The rationale is that you may want to import this module into the
main syntax module of your definition in some cases, whereas you generally do
not want to do this with the version of the module that includes all the 
functions over the `Bool` sort. For example, if you were defining the semantics
of C++, you might import `BOOL-SYNTAX` into the syntax module of your
definition, because `true` and `false` are part of the grammar of C++, but
you would only import the `BOOL` module into the main semantics module, because
C++ defines its own syntax for and, or, and not that is different from the
syntax defined in the `BOOL` module.

Here, for example, is how we might redefine our Boolean expression calculator
to use the `Bool` sort while maintaining an idiomatic structure of modules
and imports, for the first time including the rules to calculate the values of
expressions themselves (`lesson-06-c.k`):

```k
module LESSON-06-C-SYNTAX
  imports BOOL-SYNTAX

  syntax Bool ::= "(" Bool ")" [bracket]
                > "!" Bool [function]
                > left:
                  Bool "&&" Bool [function]
                | Bool "^" Bool [function]
                | Bool "||" Bool [function]
endmodule

module LESSON-06-C
  imports LESSON-06-C-SYNTAX
  imports BOOL

  rule ! B => notBool B
  rule A && B => A andBool B
  rule A ^ B => A xorBool B
  rule A || B => A orBool B
endmodule
```

Note the encapsulation of syntax: the `LESSON-06-C-SYNTAX` module contains
exactly the syntax of our Boolean expressions, and no more, whereas any other
syntax needed to implement those functions is in the `LESSON-06-C` module
instead.

#### Exercise

Add an "implies" function to the above Boolean expression calculator, using the
`->` symbol to represent implication. You can look up K's builtin "implies"
function in the `BOOL` module in `domains.md`.

## Integers in K

Unlike most programming languages, where the most basic integer type is a
fixed-precision integer type, the most commonly used integer sort in K is
the `Int` sort, which represents the **mathematical** integers, ie,
arbitrary-precision integers.

K provides three main modules for import when using the `Int` sort. The first,
containing all the syntax of integers as well as all of the functions over
integers, is the `INT` module. The second, which provides just the syntax
of integer literals themselves, is the `INT-SYNTAX` module. However, unlike
most builtin sorts in K, K also provides a third module for the `Int` sort:
the `UNSIGNED-INT-SYNTAX` module. This module provides only the syntax of
**non-negative integers**, i.e., whole numbers. The reasons for this involve
lexical ambiguity. Generally speaking, in most programming languages, `-1` is
not a literal, but instead a literal to which the unary negation operator is
applied. K thus provides this module to ease in specifying the syntax of such
languages.

For detailed information about the functions available over the `Int` sort,
refer to `domains.md`. Note again how we append `Int` to the end of most of the
integer operations to ensure they do not collide with the syntax of other
programming languages.

## Exercises

1. Extend your solution from lesson 1.4, problem 2 to implement the rules
that define the behavior of addition, subtraction, multiplication, and
division. Do not worry about the case when the user tries to divide by zero
at this time. Use `/Int` to implement division. Test your new calculator
implementation by executing the arithmetic expressions you wrote as part of
lesson 1.3, problem 2. Check to make sure each computes the value you expected.

2. Combine the Boolean expression calculator from this lesson with your
solution to problem 1, and then extend the combined calculator with the `<`,
`<=`, `>`, `>=`, `==`, and `!=` expressions. Write some Boolean expressions
that combine integer and Boolean operations, and test to ensure that these
expressions return the expected truth value.

3. Compute the following expressions using your solution from problem 2:
`7 / 3`, `7 / -3`, `-7 / 3`, `-7 / -3`. Then replace the `/Int` function in
your definition with `divInt` instead, and observe how the value of the above
expressions changes. Why does this occur?

## Next lesson

Once you have completed the above exercises, you can continue to
[Lesson 1.7: Side Conditions and Rule Priority](../07_side_conditions/README.md).
