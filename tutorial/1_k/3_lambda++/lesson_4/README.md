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

where the second argument of `+`, `x`, should be bound to the top `x`, which is `1`.
However, since `callcc` does not restore the environment, that `x` should
be looked up in the wrong, callcc-inner environment, so we should see the
overall result `4`.

Hm, we get the right result, `3` ... This sort of thing is quite annoying when
it happens.  So, why do we get `3`?  Well, recall that `+` is strict, which means
that it can evaluate its arguments in any order.  It just happened that in the
execution that we saw, its second argument was evaluated first, to `1`, and then
the `callcc` was evaluated, but its `cc` value K had already included the `1` instead
of `x` ...  In Part 4 of the tutorial we will see how to explore all non-deterministic 
behaviors of a program; we could use that feature of K to debug semantics, too.

There are two simple ways to fix this problem and thus illustrate the semantic
problem that we have here.  One is to make `+` `seqstrict` in the semantics, to
enforce its evaluation from left-to-right.  Do it to convince yourself that
the program evaluates to `4` then.  Another is to modify the program, to
enforce the left-to-right evaluation order using let binders, as we do in
`callcc-env2.lambda`:

    let x = 1 in
      let a = callcc lambda k . (let x = 2 in (k x)) in
        let b = x in
	      (a + b)

Now we also get `4`.

So the morale is: Do not reuse blindly.  *Think!*

In the next lesson we fix the environment-based semantics of `callcc` by having
`cc` also wrap an environment, besides a computation.  We will also give a more
direct semantics to recursion, based on environments instead of fixed-point
combinators.
