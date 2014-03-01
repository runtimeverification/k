### A Naive Substitution-based Polymorphic Type Inferencer

[MOVIE []]()

In this lesson you learn how little it takes to turn a naive monomorphic
type inferencer into a naive polymorphic one, basically only changing
a few characters.  In terms of the K framework, you will learn that
you can have complex combinations of substitutions in K, both over
expressions and over types.

Let us start directly with the change.  All we have to do is to take
the LAMBDA type inferencer in Lesson 4 and only change the macro

    rule let X = E in E' => (lambda X . E') E  [macro]

as follows:

    rule let X = E in E' => E'[E/X]  [macro]

In other words, we are inlining the beta-reduction rule of
lambda-calculus within the original rule.  In terms of typing,
the above forces the type inferencer to type `E` in place for each
occurrence of `X` in `E'`.  Unlike in the first rule, where `X` had to get
one type only which satisfied the constrains of all `X`'s occurrences in
`E'`, we now never associate any type to `X` anymore.

Let us `kompile` and `krun` some examples.  Everything that worked with
the type inferencer in Lesson 4 should still work here, although the
types of some programs can now be more general.  For example, reconsider
the `nested-lets.lambda` program

    let f1 = lambda x . x in
      let f2 = f1 in
        let f3 = f2 in
          let f4 = f3 in
            let f5 = f4 in
              if (f5 true) then f2 else f3

which was previously typed to `bool -> bool`.  With the new rule above,
the sequence of lets is iteratively eliminated and we end up with the
program

    if (lambda x . x) true then (lambda x . x) else (lambda x . x)

which now types (with both type inferencers) to a type of the form
`t -> t`, for some type variable `t`, which is more general than the
previous `bool -> bool` type that the program typed to in Lesson 4.

We can also now type programs that were not typable before, such as

    let id = lambda x . x
    in if (id true) then (id 1) else (id 2)

and

    let id = lambda x . x
    in id id

Let us also test it on some trickier programs, also not typable
before, such as

    let f = lambda x . x
    in let g = lambda y . f y
       in g g

which gives us a type of the form `t -> t` for some type variable `t`,
and as

    let f = let g = lambda x . x
            in let h = lambda x . lambda x . (g g g g)
               in h
    in f

which types to `t1 -> t2 -> t3 -> t3` for some type variables `t1`, `t2`, `t3`.

Here is another program which was not typable before, which is
trickier than the others above in that a lambda-bound variable appears
free in a let-bound expression:

    lambda x . (
      let y = lambda z . x
      in if (y true) then (y 1) else (y (lambda x . x))
    )

The above presents no problem now, because once `lambda z . x` gets
substituted for `y` we get a well-typed expression which yields that `x`
has the type `bool`, so the entire expression types to `bool -> bool`.

The cheap type inferencer that we obtained above therefore works as
expected.  However, it has two problems which justify a more advanced
solution.  First, substitution is typically considered an elegant
mathematical instrument which is not too practical in implementations,
so an implementation of this type inferencer will likely be based on
type environments anyway.  Additionally, we mix two kinds of
substitutions in this definition, one where we substitute types and
another where we substitute expressions, which can only make things
harder to implement efficiently.  Second, our naive substitution of `E`
for `X` in `E'` can yield an exponential explosion in size of the original
program.  Consider, for example, the following classic example which
is known to generate a type whose size is exponential in the size of
the program (and is thus used as an argument for why let-polymorphic
type inference is exponential in the worst-case):

    let f00 = lambda x . lambda y . x in
      let f01 = lambda x . f00 (f00 x) in
        let f02 = lambda x . f01 (f01 x) in
          let f03 = lambda x . f02 (f02 x) in
            let f04 = lambda x . f03 (f03 x) in
              // ... you can add more nested lets here
              f04

The particular instance of the pattern above generates a type which
has 17 type variables!  The desugaring of each `let` doubles the size of
the program and of its resulting type.  While such programs are little
likely to appear in practice, it is often the case that functions can
be quite complex and large while their type can be quite simple in the
end, so we should simply avoid retyping each function each time it is
used.

This is precisely what we will do next.  Before we present the classic
let-polymorphic type inferencer in Lesson 9, which is based on
environments, we first quickly discuss in Lesson 8 an intermediate
step, namely a naive environment-based variant of the inferencer
defined here.
