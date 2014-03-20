### Environment-Based Higher-Order Type Systems

[MOVIE []]()

In this lesson you learn how to define an environment-based type system for
a higher-order language, namely the LAMBDA language defined in Part 1 of the tutorial.

The simplest and fastest way to proceed is to copy the substitution-based
type system of LAMBDA from the previous lesson and modify it into an
environment-based one.  A large portion of the substitution-based definition
will remain unchanged.  We only have to modify the rules that use
substitution.

We do not need the substitution anymore, so we can remove the require and
import statements.  The syntax of types and expressions stays unchanged, but
we can now remove the binder tag of lambda.

Like in the type system of IMP++ in Lesson 1, we need a configuration that
contains, besides the `<k/>` cell, a `<tenv/>` cell that will hold the type
environment.

In an environment-based definition, unlike in a substitution-based one, we
need to lookup variables in the environment.  So let us start with the
type lookup rule:

    rule <k> X:Id => T ...</k> <tenv>... X |-> T ...</k>

The type environment is populated by the semantic rule of `lambda`:

    rule <k> lambda X : T . E => (T -> E) ~> tenv(Rho) ...</k>
         <tenv> Rho => Rho[T/X] </tenv>

So `X` is bound to its type `T` in the type environment, and then `T -> E`
is scheduled for processing.  Recall that the arrow type construct has been
extended into a strict expression construct, so `E` will be eventually reduced
to its type.  Like in other environment-based definitions, we need to make
sure that we recover the type environment after the computation in the scope
of the declared variable terminates.

The typing rule of application does not change, so it stays as elegant as it
was in the substitution-based definition:

    rule (T1 -> T2) T1 => T2

So do the rules for arithmetic and Boolean constructs, and those for the
`if`, and `let`, and `letrec`.

The `mu` rule needs to change, because it was previously defined using
substitution.  We modify it in the same spirit as we modified the `lambda`
rule: bind `X` to its type in the environment, schedule its body for typing
in its right context, and then recover the type environment.

Finally, we give the semantics of environment recovery, making sure
the environment is recovered only after the preceding computation is
reduced to a type:

    rule <k> _:Type ~> (tenv(Rho) => .) ...</k> <tenv> _ => Rho </tenv>

The changes that we applied to the substitution-based definition were
therefore quite systematic: each substitution invocation was replaced with
an appropriate type environment update/recovery.
