---
copyright: Copyright (c) Runtime Verification, Inc. All Rights Reserved.
---

Define LAMBDA using the S/K combinators instead of substitution.
You new definition will not require the `substitution.k` module anymore,
and will not use environments (discussed in future lectures), either.

Recall that the `S` and `K` combinators are defined as follows:

    K E1 E2 = E1
    S E1 E2 E3 = E1 E3 (E2 E3)

where the application is that of LAMBDA (left associative binary operation),
and that the lambda construct can be desugared to combinators using the
following simple rules:

    lambda X . X = S K K
    lambda X . Y = K Y    when Y is a name different from X
    lambda X . (E1 E2) = S (lambda X . E1) (lambda X . E2)
    lambda X . B = K B    when B is any constant, including S or K

To distinguish the `S` and `K` combinators from K variables and make them
more visible, we prefer to write them as `SS` and `KK` instead of `S` and `K`.

If defined correctly and completely, all the tests should pass when you call
`ktest` on the provided `config.xml` file.  The tests include all the programs
previously executed using LAMBDA (lesson_8), plus the additional program of
the mu-derived exercise, plus a few more simple programs given with this
exercise to help you better test your definition and nail down the notation.

The syntax of the new LAMBDA should be the same as before, although
`mu` needs to be desugared as in the mu-desugared exercise (using a macro).
The tricky part is how to deal with the builtin operations.  For example,
`lambda x . if x then y else z` cannot be transformed into combinators as is,
but it can if we assume a builtin conditional function constant, say `cond`,
and desugar `if_then_else_` to it.  Then this expression becomes
`lambda x . (((cond x) y) z)`, which we know how to transform.  The drawback
of this `cond` constant approach is that it may induce non-termination
in recursive programs, but that appears to not be a problem in our examples.

You will have to do the same for all builtin functions, and you will have
to make sure that you define your values correctly!  In our previous
definition we were able to say that `lambda x . e` was a value, but now that
is not possible anymore, because the lambda construct will be eliminated.
Instead, you will have to explicitly say it using the `isVal` membership
predicate that all the expressions that involve builtin functions and
yield functions are values; for example, `isVal(cond V:Val) => true` and
`isVal(cond V1:Val V2:Val) => true` need to be added, but obviously not
`isVal(cond V1:Val V2:Val V3:Val) => true`.
