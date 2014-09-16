### Multiple Binding Constructs

[MOVIE [2'40"]](http://youtu.be/Ox4uXDpcY64)

Here we learn how multiple language constructs that bind variables can coexist.
We will also learn about or recall another famous binder besides `lambda`,
namely `mu`, which can be used to elegantly define all kinds of interesting
fixed-point constructs.

The `mu` binder has the same syntax as lambda, except that it replaces
`lambda` with `mu`.

Since `mu` is a binder, in order for substitution to know how to deal with
variable capture in the presence of `mu`, we have to tell it that `mu` is a binding
construct, same like lambda.  We take advantage of being there and also add `mu`
its desired latex attribute.

The intuition for

    mu x . e

is that it reduces to `e`, but each free occurrence of `x` in `e` behaves like a
pointer that points back to `mu x . e`.

With that in mind, let us postpone the definition of `mu` and instead redefine
`letrec F X = E in E'` as a derived construct, assuming `mu` available.  The idea
is to simply regard `F` as a fixed-point of the function

    lambda X . E

that is, to first calculate

    mu F . lambda X . E

and then to evaluate `E'` where `F` is bound to this fixed-point:

    let F = mu F . lambda X . E in E'

This new definition of letrec may still look a bit tricky, particularly because
`F` is bound twice, but it is much simpler and cleaner than our previous
definition.  Moreover, now it is done in a type-safe manner (this aspect goes
beyond our objective in this tutorial).

Let us now define the semantic rule of `mu`.

The semantics of `mu` is actually disarmingly simple.  We just have to substitute
`mu X . E` for each free occurrence of `X` in `E`:

    mu X . E => E[(mu X . E) / X]

Compile `lambda.k` and execute some recursive programs.  They should be now
several times faster.  Write a few more recursive programs, for example ones
for calculating the Ackermann function, for calculating the number of moves
needed to solve the Hanoi tower problem, etc.

We have defined our first programming language in K, which allows us to
write interesting functional programs.  In the next lesson we will learn how to
fully document our language definition, in order to disseminate it, to ship it
to colleagues or friends, to publish it, to teach it, and so on.
