### A Naive Environment-Based Type Inferencer

[MOVIE []]()

In this lesson you learn how to define a naive environment-based type
inferencer for a higher-order language.  Specifically, we take the
substitution-based type inferencer for LAMBDA defined in Lesson 4 and
turn it into an environment-based one.

Recall from Lesson 3, where we defined an environment-based type
checker for LAMBDA based on the substitution-based one in Lesson 2,
that the transition from a substitution-based definition to an
environment-based one was quite systematic and mechanical: each
substitution occurrence `E[T/X]` is replaced by `E`, but at the same time
the variable `X` is bound to type `T` in the type environment.  One benefit
of using type environments instead of substitution is that we replace
a linear complexity operation (the substitution) with a constant
complexity one (the variable lookup).

There is not much left to say which has not been already said in
Lesson 3: we remove the unnecessary binder annotations for the
variable binding operations, then add a `<tenv/>` cell to the
configuration to hold the type environment, then add a new rule for
variable lookup, and finally apply the transformation of substitutions
`E[T/X]` into `E` as explained above.

The resulting type inferencer should now work exactly the same way as
the substitution-based one, except, of course, that the resulting
configurations will contain a `<tenv/>` cell now.

As sanity check, let us consider two more LAMBDA programs that test
the static scoping nature of the inferencer.  We do that because
faulty environment-based definitions often have this problem.  The
program

    let x = 1
    in let f = lambda a . x
       in let x = true
          in f 3

should type to `int`, not to `bool`, and so it does.  Similarly, the
program

    let y = 0
    in letrec f x = if x <= 0
                    then y
                    else let y = true
                         in f (x + 1)
       in f 1

should also type to `int`, not `bool`, and so it does, too.

The type inferencer defined in this lesson has the same limitations,
in terms of polymorphism, as the one in Lesson 4.  In the next
lesson we will see how it can be parallelized, and in further lessons
how to make it polymorphic.
