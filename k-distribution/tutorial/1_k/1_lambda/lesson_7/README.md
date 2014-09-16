### Derived Constructs, Extending Predefined Syntax

[MOVIE [5'10"]](http://youtu.be/qZWiBaN7zrw)

In this lesson we will learn how to define derived language constructs, that
is, ones whose semantics is defined completely in terms of other language
constructs.  We will also learn how to add new constructs to predefined
syntactic categories.

When defining a language, we often want certain language constructs to be
defined in terms of other constructs.  For example, a let-binding construct
of the form

    let x = e in e'

is nothing but syntactic sugar for

    (lambda x . e') e

This can be easily achieved with a rule, as shown in `lambda.k`.

As a side point, which is not very relevant here but good to know, we may
want the *desugaring* of `let` to not even count as a computational step, but
as a mere *structural rearrangement* of the program so that other semantic
rules (beta reduction, in our case) can match and apply.

The K tool allows us to tag rules with the attribute `structural`, with
precisely the intuition above.  You can think of structural rules as a kind
of light rules, almost like macros, or like ones which apply *under the hood*,
instantaneously.  There are several other uses for structural rules in K,
which we will discuss later in this tutorial.

Compile `lambda.k` and write some programs using `let` binders.  

For example, consider a `lets.lambda` program which takes `arithmetic.lambda`
and replaces each integer by a let-bound variable.  It should evaluate to
`true`, just like the original `arithmetic.lambda`.

Let us now consider a more interesting program, namely one that calculates the
factorial of 10:

    let f = lambda x . (
            (lambda t . lambda x . (t t x))
            (lambda f . lambda x . (if x <= 1 then 1 else (x * (f f (x + -1)))))
            x
          )
    in (f 10)

This program follows a common technique to define fixed points in untyped
lambda calculus, based on passing a function to itself.

We may not like to define fixed points following the approach above, because
it requires global changes in the body of the function meant to be recursive,
basically to pass it to itself (`f f` in our case above).  The approach below
isolates the fixed point aspect of the function in a so-called *fixed point
combinator*, which we call `fix` below, and then apply it to the function
defining the body of the factorial, without any changes to it:

    let fix = lambda f . (
              (lambda x . (f (lambda y . (x x y))))
              (lambda x . (f (lambda y . (x x y))))
            )
    in let f = fix (lambda f . lambda x .
                    (if x <= 1 then 1 else (x * (f (x + -1)))))
       in (f 10)

Although the above techniques are interesting and powerful (indeed, untyped
lambda calculus is in fact Turing complete), programmers will probably not
like to write programs this way.

We can easily define a more complex derived construct, called `letrec` and
conventionally encountered in functional programming languages, whose semantics
captures the fixed-point idea above.  In order to keep its definition simple
and intuitive, we define a simplified variant of `letrec`, namely one which only
allows to define one recursive one-argument function.  See `lambda.k`.

There are two interesting observations here.

First, note that we have already in-lined the definition of the `fix`
combinator in the definition of the factorial, to save one application of the 
beta reduction rule (and the involved substitution steps).  We could have
in-lined the definition of the remaining `let`, too, but we believe that the
current definition is easier to read.

Second, note that we extended the predefined `Id` syntactic category with two
new constants, `$x` and `$y`.  The predefined identifiers cannot start with
`$`, so programs that will be executed with this semantics cannot possibly
contain the identifiers $x and $y.  In other words, by adding them to Id they
become indirectly reserved for the semantics.  This is indeed desirable,
because any possible uses of $x in the body of the function defined
using `letrec` would be captured by the `lambda $x` declaration in the
definition of `letrec`.

Using `letrec`, we can now write the factorial program as elegantly as it can
be written in a functional language:

    letrec f x = if x <= 1 then 1 else (x * (f (x + -1)))
    in (f 10)

In the next lesson we will discuss an alternative definition of `letrec`, based
on another binder, `mu`, specifically designed to define fixed points.
