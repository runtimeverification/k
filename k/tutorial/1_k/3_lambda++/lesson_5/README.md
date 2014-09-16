### More Semantic Computation Items

[MOVIE [5'19"]](http://youtu.be/dP3FW0kZN6k)

In this lesson we see more examples of semantic (i.e., non-syntactic)
computational items, and how useful they can be.  Specifically, we fix the
environment-based definition of `callcc` and give an environment-based
definition of the `mu` construct for recursion.

Let us first fix `callcc`.  As discussed in Lesson 4, the problem that we noticed
there was that we only recovered the computation, but not the environment, when
a value was passed to the current continuation.  This is quite easy to fix:
we modify `cc` to take both an environment and a computation, and its rules
to take a snapshot of the current environment with it, and to recover it at
invocation time:

    syntax Val ::= cc(Map,K)
    rule <k> (callcc V:Val => V cc(Rho,K)) ~> K </k> <env> Rho </env>
    rule <k> cc(Rho,K) V ~> _ =>  V ~> K </k> <env> _ => Rho </env>

Let us kompile and make sure it works with the `callcc-env2.lambda` program,
which should evaluate to `3`, not to `4`.

Note that the `cc` value, which can be used as a computation item in the `<k/>`
cell, is now quite semantic in nature, pretty much the same as the closures.

Let us next add one more closure-like semantic computational item, for `mu`.
But before that, let us reuse the semantics of `letrec` in terms of `mu` that
was defined in Lesson 8 of Part 1 of the tutorial on LAMBDA:

    syntax Exp ::= "letrec" Id Id "=" Exp "in" Exp
                 | "mu" Id "." Exp      [latex(\mu{#1}.{#2})]
    rule letrec F:Id X = E in E' => let F = mu F . lambda X . E in E'
      [structural]

We removed the `binder` annotation of `mu`, because it is not necessary
anymore (since we do not work with substitutions anymore).

To save the number of locations needed to evaluate `mu X . E`, let us replace
it with a special closure which already binds `X` to a fresh location holding the
closure itself:

    syntax Exp ::= muclosure(Map,Exp)

    rule <k> mu X . E => muclosure(Rho[N/X],E) ...</k>
         <env> Rho </env>
         <store>... . => (N |-> muclosure(Rho[N/X],E)) ...</store>
      when fresh(N:Nat)  [structural]

Since each time `mu X . E` is encountered during the evaluation it needs to
evaluate `E`, we conclude that `muclosure` cannot be a value.  We can declare it
as either an expression or as a computation.  Let's go with the former.

Finally, here is the rule unrolling the `muclosure`:

    rule <k> muclosure(Rho,E) => E ~> env(Rho') ...</k>
         <env> Rho' => Rho </env>

Note that the current `environment Rho'` needs to be saved before and
restored after `E` is executed, because the fixed point may be invoked
from a context with a completely different environment from the one
in which `mu X . E` was declared.

We are done.  Let us now `kompile` and `krun` `factorial-letrec.lambda` from
Lesson 7 in Part 1 of the tutorial on LAMBDA.  Recall that in the previous lesson
this program generated a lot of garbage into the store, due to the
need to allocate space for the arguments of all those lambda abstractions
needed to run the fixed-point combinator.  Now we need much fewer locations,
essentially only locations for the argument of the factorial function, one at
each recursive call.  Anyway, much better than before.

In the next lesson we wrap up the environment definition of LAMBDA++ and
generate its documentation.
