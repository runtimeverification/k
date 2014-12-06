<!-- Copyright (c) 2014 K Team. All Rights Reserved. -->
### Do Not Reuse Blindly!

[MOVIE [3'37"]](http://youtu.be/OXvtklaSaSQ)

It may be tempting to base your decision to reuse an existing semantics of
a language feature solely on syntactic considerations; for example, to reuse
whenever the parser does not complain.  As seen in this lesson, this could
be quite risky.

Let's try (and fail) to reuse the definition of `callcc` from Lesson 1:

    syntax Exp ::= "callcc" Exp  [strict]
    syntax Val ::= cc(K)
    rule <k> (callcc V:Val => V cc(K)) ~> K </k>
    rule <k> cc(K) V ~> _ =>  V ~> K </k>

The callcc examples that we tried in Lesson 1 work, so it may look it works.

However, the problem is that `cc(K)` should also include an environment,
and that environment should also be restored when `cc(K)` is invoked.
Let's try to illustrate this bug with `callcc-env1.lambda`

    let x = 1 in
      ((callcc lambda k . (let x = 2 in (k x))) + x)

where the second argument of `+`, `x`, should be bound to the top `x`, which
is `1`.  However, since `callcc` does not restore the environment, that `x`
should be looked up in the wrong, callcc-inner environment, so we should see
the overall result `4`.

Hm, we get the right result, `3` ... This sort of thing is quite annoying
when it happens.  So, why do we get `3`?  Well, recall that `+` is strict,
which means that it can evaluate its arguments in any order.  It just
happened that in the execution that we saw, its second argument was evaluated
first, to `1`, and then the `callcc` was evaluated, but its `cc` value K had
already included the `1` instead of `x` ...  In Part 4 of the tutorial we will
see how to explore all non-deterministic behaviors of a program; we could use
that feature of K to debug semantics, too.  For example, in this case, we
could search for all behaviors of this program and we would indeed get two
possible value results: 3 and 4.

NOTE: we warn the reader that the result 3 above was obtained with version 3.4
of the K implementation.  Different versions may employ different execution
orders in non-deterministic program, so it can be quite possible that the
program above may evaluate to 4 with another version of K.

One may think that the problem is the non-deterministic evaluation order
of `+`, and thus that all we need to do is to enforce a deterministic order
in which the arguments of + are evaluated.  Let us follow this path to
see what happens.  There are two simple ways to make the evaluation order
of `+`'s arguments deterministic.  One is to make `+` `seqstrict` in the
semantics, to enforce its evaluation from left-to-right.  Do it and then
run the program above again; you should get only one behavior for the
program above, 4, which therefore shows that copy-and-pasting our old
definition of callcc was incorrect.  However, as seen shortly, that only
fixed the problem for the particular example above, but not in general.
Another conventional approach to enforce the desired evaluation order is to
modify the program to enforce the left-to-right evaluation order using let
binders, as we do in `callcc-env2.lambda`:

    let x = 1 in
      let a = callcc lambda k . (let x = 2 in (k x)) in
        let b = x in
	      (a + b)

With version 3.5 of K, we get the expected result `4` when we execute this
program, so it may look like our non-deterministic problem is fixed.
Unfortunately, it is not.  Using the K tool to search for all the behaviors
in the program above reveals that the final result `3` is still possible.
Moreover, both the `3` and the `4` behaviors are possible regardless of whether
`+` is declared to be `seqstrict` or just `strict`.  How is that possible?
The problem is now the non-deterministic evaluation strategy of the function
application construct.  Indeed, recall that the semantics of the let-in
construct is defined by desugaring to lambda application:

    rule let X = E in E' => (lambda X . E') E     [macro]

With this, the program above eventually reduces to

    (lambda a . ((lambda b . a + b) x))
    (callcc lambda k . (let x = 2 in (k x)))

in an environment where `x` is `1`.  If the first expression evaluates first,
then it does so to a closure in which `x` is bound to a location holding `1`,
so when applied later on to the `x` inside the argument of `callcc` (which is
`2`), it will correctly lookup `x` in its enclosed environment and thus the
program will evaluate to `3`.  On the other hand, if the second expression
evaluates first, then the `cc` value will freeze the first expression as is,
breaking the relationship between its `x` and the current environment in which
it is bound to `1`, being inadvertently captured by the environment of the
let-in construct inside the `callcc` and thus making the entire expression
evaluate to `4`.

So the morale is: Do not reuse blindly.  *Think!*

In the next lesson we fix the environment-based semantics of `callcc` by having
`cc` also wrap an environment, besides a computation.  We will also give a more
direct semantics to recursion, based on environments instead of fixed-point
combinators.
