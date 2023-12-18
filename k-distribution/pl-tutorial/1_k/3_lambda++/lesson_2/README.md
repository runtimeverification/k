---
copyright: Copyright (c) Runtime Verification, Inc. All Rights Reserved.
---

# Semantic (Non-Syntactic) Computation Items

In this lesson we start another semantic definition of LAMBDA++, which
follows a style based on environments instead of substitution.  In terms of
K, we will learn how easy it is to add new items to the syntactic category
of computations `K`, even ones which do not have a syntactic nature.

An environment binds variable names of interest to locations where their
values are stored.  The idea of environment-based definitions is to maintain
a global *store* mapping locations to values, and then have environments
available when we evaluate expressions telling where the variables are
located in the store.  Since LAMBDA++ is a relatively simple language, we
only need to maintain one global environment.  Following a similar style
like in IMP, we place all cells into a top cell `T`:

    configuration <T>
                    <k> $PGM:Exp </k>
                    <env> .Map </env>
                    <store> .Map </store>
                  </T>

Recall that `$PGM` is where the program is placed by `krun` after parsing.  So
the program execution starts with an empty environment and an empty store.

In environment-based definitions of lambda-calculi, lambda abstractions
evaluate to so-called *closures*:

    rule <k> lambda X:Id . E => closure(Rho,X,E) ...</k>
	     <env> Rho </env>

A closure is like a lambda abstraction, but it also holds the environment
in which it was declared.  This way, when invoked, a closure knows where to
find in the store the values of all the variables that its body expression
refers to.  We will define the lookup rule shortly.

Therefore, unlike in the substitution-based definitions of LAMBDA and
LAMBDA++, neither the lambda abstractions nor the identifiers are values
anymore here, because they both evaluate further: lambda abstractions to
closures and identifiers to their values in the store.  In fact, the only
values at this moment are the closures, and they are purely semantic entities,
which cannot be used explicitly in programs.  That's why we modified the
original syntax of the language to include no `Val` syntactic category
anymore, and that's why we need to add closures as values now; same like
before, we add a `Val` syntactic category which is subsorted
to `KResult`.  In general, whenever you have any strictness attributes,
your should also define some K results.

Invoking a closure is a bit more involved than the substitution-based
beta-reduction: we need to switch to the closure's environment, then create a
new, or fresh, binding for the closure's parameter to the value passed to the
closure, then evaluate the closure's body, and then switch back to the
caller's environment, which needs to be stored somewhere in the meanwhile.
We can do all these with one rule:

    rule <k> closure(Rho,X,E) V:Val => E ~> Rho' ...</k>
         <env> Rho' => Rho[X <- !N] </env>
         <store>... .Map => (!N:Int |-> V) ...</store>

Therefore, we atomically do all the following:

- switch the computation to the closure's body, `E`, followed by a
caller-environment-recovery task `Rho'` (note that `Rho'` is the
current environment),
- generate a fresh location `!N` (the `!` is important, we discuss it below),
bind `X` to `!N` in closure's environment and switch the current environment
`Rho'` to that one,
- write the value passed to the closure, `V`, at location `!N`.

This was the most complex K rule we've seen so far in the tutorial.  Note,
however, that this one rule achieves a lot.  It is, in fact, quite compact
considering how much it does.  Note also that everything that this K rule
mentions is needed also conceptually in order to achieve this task, so it
is minimal from that point of view.  That would not be the case if we
used, instead, a conventional rewrite rule, because we would have had to
mention the remaining store, say `Sigma`, in both sides of the rule, to say
it stays unchanged.  Here we just use `...`.

The declaration of the *fresh* variable above, `!N`, is new and needs
some explanation.  First, note that `!N` appears only in the right-hand-side
terms in the rule, that is, it is not matched when the rule is applied.
Instead, a fresh `Nat` element is generated each time the rule is applied.
In K, we can define syntactic categories which have the capability to
generate fresh elements like above, using unbound variables whose name starts
with a `!`.  The details of how to do that are beyond the scope of this
tutorial (see Tutorial 6).  All we need to know here is that an arbitrary
fresh element of that syntactic category is generated each time the rule
is applied.  We cannot rely on the particular name or value of the generated
element, because that can change with the next version of the K tool, or
even from execution to execution with the same version.  All you can rely
on is that each newly generated element is distinct from the previously
generated elements for the same syntactic category.

Unlike in the substitution-based definition, we now also need a lookup rule:

    rule <k> X => V ...</k>
         <env>... X |-> N ...</env>
         <store>... N |-> V ...</store>

This rule speaks for itself: replace `X` by the value `V` located in the store
at `X`'s location `N` in the current environment.

The only thing left to define is the auxiliary environment-recovery operation:

  rule <k> _:Val ~> (Rho => .) ...</k> <env> _ => Rho </env>

When the item preceding the environment recovery task `Rho` in the
computation becomes a value, replace the current environment with `Rho`
and dissolve `Rho` from the computation.

Let us kompile and ... fail:

    kompile lambda

gives a parsing error saying that `V:Val` does not fit there in the closure
invocation rule.  That's because `Val` and `Exp` are currently completely
disconnected, so K rightfully complains that we want to apply a value to
another one, because application was defined to work with expressions, not
values.  What we forgot here was to state that `Exp` includes `Val`:

    syntax Exp ::= Val

Now everything works, but it is a good time to reflect a bit.

So we added closures, which are inherently semantic entities, to the syntax
of expressions.  Does that mean that we can now write LAMBDA programs with
closures in them?  Interestingly, with our current definition of LAMBDA,
which purposely did not follow the nice organization of IMP into syntax and
semantic modules, and with K's default parser, `kast`, you can.  But you are
not supposed to speculate this!  In fact, if you use an external parser, that
parser will reject programs with explicit closures.  Also, if we split the
LAMBDA definition into two modules, one called LAMBDA-SYNTAX containing
exclusively the desired program syntax and one called LAMBDA importing the
former and defining the syntax of the auxiliary operations and the semantics,
then even K's default parser will reject programs using auxiliary syntactic 
constructs.

Indeed, when you kompile a language, say `lang.k`, the tool will by default
attempt to find a module LANG-SYNTAX and generate the program parser from
that.  If it cannot find it, then it will use the module LANG instead.  There
are also ways to tell kompile precisely which syntax module you want to use
for the program parser if you don't like the default convention.
See `kompile --help`.

Another insightful thought to reflect upon, is the relationship between your
language's values and other syntactic categories.  It is often the case that
values form a subset of the original language syntax, like in IMP (Part 2 of
the tutorial), but sometimes that is not true, like in our case here.  When
that happens, in order for the semantics to be given smoothly and uniformly
using the original syntax, you need to extend your language's original
syntactic categories with the new values.  The same holds true in other
semantic approaches, not only in K, even in ones which are considered purely 
syntactic.  As it should be clear by now, K does not enforce you to use a
purely syntactic style in your definitions; nevertheless, K does allow you to 
develop purely syntactic definitions, like LAMBDA in Part 1 of the tutorial,
if you prefer those.

`krun` some programs, such as those provided in Lesson 1 of the LAMBDA
tutorial (Part 1).  Note the closures, both as results in the `<k/>` cell,
and as values in the store.  Also, since variables are not values anymore,
expressions that contain free variables may get stuck with one of those on
top of their computation.  See, for example, `free-variable-capture.lambda`,
which gets stuck on `z`, because `z` is free, so it cannot evaluate it.
If you want, you can go ahead and manually provide a configuration with
`z` mapped to some location in the environment and that location mapped to
some value in the store, and then you can also execute this program.  The
program `omega.lambda` should still loop.

Although we completely changed the definitional style of LAMBDA, the semantics
of the other constructs do not need to change, as seen in the next lesson.


Go to [Lesson 3, LAMBDA++: Reusing Existing Semantics](../lesson_3/README.md).

[MOVIE (out of date) [8'02"]](https://youtu.be/BYhQQW6swfc)
