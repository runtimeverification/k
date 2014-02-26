### Abrupt Changes of Control

[MOVIE [6'28"]](http://youtu.be/UZ9iaus024g)

Here we add *call-with-current-continuation* (`callcc`) to the definition of
LAMBDA completed in Tutorial 1, and call the resulting language LAMBDA++.
While doing so, we will learn how to define language constructs that
abruptly change the execution control flow.

Take over the `lambda.k` definition from Lesson 8 in Part 1 of this Tutorial, which
is the complete definition of the LAMBDA language, but without the comments.

`callcc` is a good example for studying the capabilities of a framework to
support abrupt changes of control, because it is one of the most
control-intensive language constructs known.  Scheme is probably the first
programming language that incorporated the `callcc` construct, although
similar constructs have been recently included in many other languages in
one form or another.

Here is a quick description: `callcc e` passes the remaining computation
context, packaged as a function `k`, to `e` (which is expected to be a function);
if `e` passes anything to `k`, then the current execution context is discarded and
replaced by the one encoded by `k`; if `e` evaluates normally to `v` and passes
nothing to `k`, then `v` is returned as a result of `callcc e` and the execution
continues normally.  For example, we want the program `callcc-jump.lambda`:

    (callcc (lambda k . ((k 5) + 2))) + 10

to evaluate to `15`, not `17`!  Indeed, the computation context `[] + 10` is
passed to `callcc`'s argument, which then sends it a `5`, so the computation
resumes to `5 + 10`.  On the other hand, the program `callcc-not-jump.lambda`

    (callcc (lambda k . (5 + 2))) + 10

evaluates to `17`.

If you like playing games, you can metaphorically thing of `callcc e` as
*saving your game in a file and passing it to your friend `e`*.  Then `e`
can decide at some moment to drop everything she was doing, load your game
and continue to play it from where you were.

The behavior of many popular control-changing constructs can be obtained
using `callcc`.  The program `return.lambda` shows, for example, how to
obtain the behavior of a `return` statement, which leaves the current execution
context inside a function and returns a value to the caller's context:

    letrec f x = callcc (lambda return . (
      f (if (x <= 0) then ((return 1) / 0) else 2)
    ))
    in (f -3)

This should evaluate to `1`, in spite of the recursive call to `f`
and of the division by zero!  Note that `return` is nothing but a variable
name, but one which is bound to the current continuation at the beginning of
the function execution.  As soon as `1` is passed to `return`, the computation
jumps *back in time* to where `callcc` was defined! Change `-3` to `3` and the
program will loop forever.

`callcc` is quite a powerful and beautiful language construct, although one
which is admittedly hard to give semantics to in some frameworks.
But not in K :)  Here is its entire K syntax and semantics of `callcc`:

    syntax Exp ::= "callcc" Exp  [strict]
    syntax Val ::= cc(K)
    rule <k> (callcc V:Val => V cc(K)) ~> K </k>
    rule <k> cc(K) V ~> _ =>  V ~> K </k>

Let us first discuss the annotated syntax.  We declared `callcc` strict,
because its argument may not necessarily be a function yet, so it may need
to be evaluated.  As explained above, we need to encode the remaining
computation somehow and pass it to `callcc`'s argument.  More specifically,
since LAMBDA is call-by-value, we have to encode the remaining computation as
a value.  We do not want to simply subsort computations to `Val`, because there
are computations which we do not want to be values.  A simple solution to
achieve our goal here is to introduce a new value construct, say `cc` (from
*current-continuation*), which holds any computation.

Note that, inspired from [SDF](http://www.program-transformation.org/Sdf/),
K allows you to define the syntax of helping semantic operations, like `cc`,
more compactly.  Typically, we do not need a fancy syntax for such operators;
all we need is a name, followed by open parenthesis, followed by a
comma-separated list of arguments, followed by closed parenthesis.  If this
is the syntax that you want for a particular construct, then K allows you to
drop all the quotes surrounding the terminals.

The semantic rules do exactly what the English semantics of `callcc` says.
Note that here, unlike in our definition of LAMBDA in Tutorial 1, we had
to mention the cell `<k/>` in our rules.  This is because we need to make sure
that we match the entire remaining computation, not only a fragment of it!
For example, if we replace the two rules above with

    rule (callcc V:Val => V cc(K)) ~> K
    rule cc(K) V ~> _ =>  V ~> K

then we get a `callcc` which is allowed to non-deterministically pick a
prefix of the remaining computation and pass it to its argument, and then
when invoked within its argument, a non_deterministic prefix of the new
computation is discarded and replaced by the saved one.  Wow, that would
be quite a language!  Would you like to write programs in it?  :)

Consequently, in K we can abruptly change the execution control flow of a
program by simply changing the contents of the `<k/>` cell.  This is one of
the advantages of having an explicit representation of the execution context,
like in K or in reduction semantics with evaluation-contexts.  Constructs like
`callcc` are very hard and non-elegant to define in frameworks such as SOS,
because those implicitly represent the execution context as proof context,
and the latter cannot be easily changed.

Now that we know how to handle cells in configurations and use them in rules,
in the next lesson we take a fresh look at LAMBDA and define it using
an environment-based style, which avoids the complexity of substitution
(e.g., having to deal with variable capture) and is closer in spirit to how
functional languages are implemented.
