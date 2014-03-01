### Let-Polymorphic Type Inferencer (Damas-Hindley-Milner)

[MOVIE []]()

In this lesson we discuss a type inferencer based on what we call today
*the Damas-Hindley-Milner type system*, which is at the core of many
modern functional programming languages.  The first variant of it was
proposed by Hindley in 1969, then, interestingly, Milner rediscovered
it in 1978 in the context of the ML language.  Damas formalized it as
a type system in his PhD thesis in 1985.  More specifically, our type
inferencer here, like many others as well as many implementations of
it, follows more closely the syntax-driven variant proposed by Clement
in 1987.

In terms of K, we will see how easily we can turn one definition which
is considered naive (our previous type inferencer in Lesson 8) into a
definition which is considered advanced.  All we have to do is to
change one existing rule (the rule of the let binder) and to add a new
one.  We will also learn some new predefined features of K, which make
the above possible.

The main idea is to replace the rule

    rule let X = E in E' => E'[E/X]  [macro]

which creates potentially many copies of `E` within `E'` with a rule
which types `E` once and then reuses that type in each place where `X`
occurs free in `E'`.  The simplest K way to type `E` is to declare the
let construct `strict(2)`.  Now we cannot simply bind `X` to the type
of `E`, because we would obtain a variant of the naive type inferencer
we already discussed, together with its limitations, in Lesson 5 of this
tutorial.  The trick here is to parameterize the type of `E` in all its
unconstrained fresh types, and then create fresh copies of those
parameters in each free occurrence of `X` in `E'`.

Let us discuss some examples, before we go into the technical details.
Consider the first let-polymorphic example which failed to be typed
with our first naive type-inferencer:

    let id = lambda x . x
    in if (id true) then (id 1) else (id 2)

When typing `lambda x . x`, we get a type of the form `t -> t`, for some
fresh type `t`.  Instead of assigning this type to `id` as we did in the
naive type inferencers, we now first parametrize this type in its
fresh variable `t`, written

    (forall t) t -> t

and then bind `id` to this parametric type.  The intuition for the
parameter is that it can be instantiated with any other type, so this
parametric type stands, in fact, for infinitely many non-parametric
types.  This is similar to what happens in formal logic proof systems,
where *rule schemas* stand for infinitely many concrete instances of
them.  For this reason, parametric types are also called *type schemas*.

Now each time `id` is looked up within the let-body, we create a fresh
copy of the parameter `t`, which can this way be independently
constrained by each local context.  Let's suppose that the three `id`
lookups yield the types `t1 -> t1`, `t2 -> t2`, and respectively `t3 -> t3`.
Then `t1` will be constrained to be `bool`, and `t2` and `t3` to be `int`,
so we can now safely type the program above to `int`.

Therefore, a type schema comprises a summary of all the typing work
that has been done for typing the corresponding expression, and an
instantiation of its parameters with fresh copies represents an
elegant way to reuse all that typing work.

There are some subtleties regarding what fresh types can be made
parameters.  Let us consider another example, discussed as part of
Lesson 7 on naive let-polymorphism:

    lambda x . (
      let y = lambda z . x
      in if (y true) then (y 1) else (y (lambda x . x))
    )

This program should type to `bool -> bool`, as explained in Lesson 7.
The `lambda` construct will bind `x` to some fresh type `tx`.  Then the
let-bound expression `lambda z . x` types to `tz -> tx` for some
additional fresh type `tz`.  The question now is what should the
parameters of this type be when we generate the type schema?  If we
naively parameterize in all fresh variables, that is in both `tz` and
`tx` obtaining the type schema `(forall tz,tx) tz -> tx`, then there will
be no way to infer that the type of `x`, `tx`, must be a `bool`!  The
inferred type of this expression would then wrongly be `tx -> t` for
some fresh types `tx` and `t`.  That's because the parameters are replaced
with fresh copies in each occurrence of `y`, and thus their relationship
to the original `x` is completely lost.  This tells us that we cannot
parameterize in all fresh types that appear in the type of the
let-bound expression.  In particular, we cannot parameterize in those
which some variables are already bound to in the current type
environment (like `x` is bound to `tx` in our example above).
In our example, the correct type schema is `(forall tz) tz -> tx`,
which now allows us to correctly infer that `tx` is `bool`.

Let us now discuss another example, which should fail to type:

    lambda x .
      let f = lambda y . x y
      in if (f true) then (f 1) else (f 2)

This should fail to type because `lambda y . x y` is equivalent to `x`,
so the conditional imposes the conflicting constraints that `x` should be
a function whose argument is either a `bool` or an `int`.  Let us try to
type it using our currently informal procedure.  Like in the previous
example, `x` will be bound to a fresh type `tx`.  Then the let-bound
expression types to `ty -> tz` with `ty` and `tz` fresh types, adding also
the constraint `tx = ty -> tz`.  What should the parameters of this type
be?  If we ignore the type constraint and simply make both `ty` and `tz`
parameters because no variable is bound to them in the type
environment (indeed, the only variable `x` in the type environment is
bound to `tx`), then we can wrongly type this program to `tx -> tz`
following a reasoning similar to the one in the example above.
In fact, in this example, none of `ty` and `tz` can be parameters, because
they are constrained by `tx`.

The examples above tell us two things: first, that we have to take the
type constraints into account when deciding the parameters of the
schema; second, that after applying the most-general-unifier solution
given by the type constraints everywhere, the remaining fresh types
appearing anywhere in the type environment are consequently constrained
and cannot be turned into parameters.  Since the type environment can in
fact also hold type schemas, which already bind some types, we only need
to ensure that none of the fresh types appearing free anywhere in the
type environment are turned into parameters of type schemas.

Thanks to generic support offered by the K tool, we can easily achieve
all the above as follows.

First, add syntax for type schemas:

    syntax TypeSchema ::= "(" "forall" Set ")" Type  [binder]

The definition below will be given in such a way that the `Set` argument
of a type schema will always be a set of fresh types.  We also declare
this construct to be a `binder`, so that we can make use of the generic
free variable function provided by the K tool.

We now replace the old macro of `let`

    rule let X = E in E' => E'[E/X]  [macro]

with the following rule:

    rule <k> let X = T:Type in E => E ~> tenv(TEnv) ...</k>
         <mgu> Theta:Mgu </mgu>
         <tenv> TEnv
          => TEnv[(forall freeVariables(applyMgu(Theta, T)) -Set
                          freeVariables(applyMgu(Theta, values TEnv))
                  ) applyMgu(Theta, T) / X]
         </tenv>

So the type `T` of `E` is being parameterized and then bound to `X` in the
type environment.  The current mgu `Theta`, which comprises all the type
constraints accumulated so far, is applied to both `T` and the types in
the type environment.  The remaining fresh types in `T` which do not
appear free in the type environment are then turned into type parameters.
The function `freeVariables` returns, as expected, the free variables of
its argument as a `Set`; this is why we declared the type schema to be a
binder above.

Now a LAMBDA variable in the type environment can be bound to either a
type or a type schema.  In the first case, the previous rule we had
for variable lookup can be reused, but we have to make sure we check
that `T` there is of sort `Type` (adding a sort membership, for example).
In the second case, as explained above, we have to create fresh copies
of the parameters.  This can be easily achieved with another
predefined K function, as follows:

    rule <k> X:Id => freshVariables(Tvs,T) ...</k>
         <tenv>... X |-> (forall Tvs) T ...</tenv>

Indeed, `freshVariables` takes a set of variables and a term, and returns the 
same term but with each of the given variables replaced by a fresh copy.

The operations `freeVariables` and `freshVariables` are useful in many K
definitions, so they are predefined in module `substitution.k`.

Our definition of this let-polymorphic type inferencer is now
complete.  To test it, `kompile` it and then `krun` all the LAMBDA
programs discussed since Lesson 4.  They should all work as expected.
