### A Naive Environment-based Polymorphic Type Inferencer

[MOVIE []]()

In this short lesson we discuss how to quickly turn a naive
environment-based monomorphic type inferencer into a naive let-polymorphic
one.  Like in the previous lesson, we only need to change a few
characters.  In terms of the K framework, you will learn how to have
both environments and substitution in the same definition.

Like in the previous lesson, all we have to do is to take the LAMBDA
type inferencer in Lesson 5 and only change the macro

    rule let X = E in E' => (lambda X . E') E  [macro]

as follows:

    rule let X = E in E' => E'[E/X]  [macro]

The reasons why this works have already been explained in the previous
lesson, so we do not repeat them here.

Since our new let macro uses substitution, we have to require the
substitution module at the top and also import SUBSTITUTION in the
current module, besides the already existing UNIFICATION.

Everything which worked with the type inferencer in Lesson 7 should
also work now.  Let us only try the exponential type example,

    let f00 = lambda x . lambda y . x in
      let f01 = lambda x . f00 (f00 x) in
        let f02 = lambda x . f01 (f01 x) in
          let f03 = lambda x . f02 (f02 x) in
            let f04 = lambda x . f03 (f03 x) in
              f04

As expected, this gives us precisely the same type as in Lesson 7.

So the only difference between this type inferencer and the one in
Lesson 7 is that substitution is only used for LAMBDA-to-LAMBDA
transformations, but not for infusing types within LAMBDA programs.
Thus, the syntax of LAMBDA programs is preserved intact, which some
may prefer.  Nevertheless, this type inferencer is still expensive and
wasteful, because the let-bound expression is typed over and over
again in each place where the let-bound variable occurs.

In the next lesson we will discuss a type inferencer based on the
classic Damas-Hindley-Milner type system, which maximizes the reuse of
typing work by means of parametric types.
