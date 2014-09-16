### Substitution-Based Higher-Order Type Systems

[MOVIE [6'52"]](http://youtu.be/7P2QtR9jM2o)

In this lesson you learn how to define a substitution-based type system for
a higher-order language, namely the LAMBDA language defined in Part 1 of the tutorial.

Let us copy the definition of LAMBDA from Part 1 of the tutorial, Lesson 8.
We are going to modify it into a type systems for LAMBDA.

Before we start, it is important to clarify an important detail, namely that
our type system will yield a type checker when executed, not a type
inferencer.  In particular, we are going to change the LAMBDA syntax
to allow us to associate a type to each declared variable.  The
constructs which declare variables are `lambda`, `let`, `letrec` and `mu`.
The syntax of all these will therefore change.

Since here we are not interested in a LAMBDA semantics anymore, we take the
freedom to eliminate the `Val` syntactic category, our previous results.
Our new results are going to be the types, because programs will now reduce
to their types.

As explained, the syntax of the `lambda` construct needs to change, to also 
declare the type of the variable that it binds.  We add the new syntactic 
category `Type`, with the following constructs: `int`, `bool`, the function
type (which gives it its higher-order status), and parentheses as bracket.
Also, we make types our K results.

We are now ready to define the typing rules.

Let us start with the typing rule for lambda abstraction: `lambda X : T . E`
types to the function type `T -> T'`, where `T'` is the type obtained by further
typing `E[T/X]`.  This can be elegantly achieved by reducing the lambda 
abstraction to `T -> E[T/X]`, provided that we extend the function type construct
to take expressions, not only types, as arguments, and to be strict.
This can be easily achieved by redeclaring it as a strict expression construct
(strictness in the second argument would suffice in this example, but it is
more uniform to define it strict overall).

The typing rule for application is as simple as it can get: `(T1->T2) T1 => T2`.

Let us now give the typing rules of arithmetic and Boolean expression
constructs.  First, let us get rid of `Val`.  Second, rewrite each value to its
type, similarly to the type system for IMP++ in the previous lesson.  Third,
replace each semantic rule by its typing rule.  Fourth, make sure you
do not forget to subsort `Type` to `Exp`, so your rules above will parse.

The typing policy of the conditional statement is that its first argument
should type to `bool` and its other two arguments should type to the same type
`T`, which will also be the result type of the conditional.  So we make the
conditional construct `strict` in all its three arguments and we write the 
obvious rule: `if bool then T:Type else T => T`.  We want a runtime check that 
the latter arguments are actually typed, so we write `T:Type`.

There is nothing special about `let`, except that we have to make sure we
change its syntax to account for the type of the variable that it binds.
This rule is a macro, so the let is desugared statically.

Similarly, the syntax of `letrec` and `mu` needs to change to account for the
type of the variable that they bind.  The typing of `letrec` remains based on
its desugaring to `mu`; we have to make sure the types are also included now.

The typing policy of `mu` is that its body should type to the same type `T` of its
variable, which is also the type of the entire mu expression.  This can be 
elegantly achieved by rewriting it to `(T -> T) E[T/X]`.  Recall that 
application is strict, so `E[T/X]` will be eventually reduced to its type.
Then the application types correctly only if that type is also `T`, and in that
case the result type will also be `T`.

`kompile` and `krun` some programs.  You can, for example, take the LAMBDA
programs from the first tutorial, modify them by adding types to their
variable declarations, and then type check them using `krun`.

In the next lesson we will discuss an environment-based type system
for LAMBDA.
