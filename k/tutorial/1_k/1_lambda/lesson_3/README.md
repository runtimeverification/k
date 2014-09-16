### Evaluation Strategies using Strictness

[MOVIE [2'20"]](http://youtu.be/aul1x6bd1YM)

Here we learn how to use the K `strict` attribute to define desired evaluation
strategies.  We will also learn how to tell K which terms are already
evaluated, so it does not attempt to evaluate them anymore and treats them
internally as results of computations.

Recall from the previous lecture that the LAMBDA program
`free-variable-capture.lambda` was stuck, because K was not given permission
to evaluate the arguments of the lambda application construct.

You can use the attribute `strict` to tell K that the corresponding construct
has a strict evaluation strategy, that is, that its arguments need to be
evaluated before the semantics of the construct applies.  The order of
argument evaluation is purposely unspecified when using `strict`, and indeed
the K tool allows us to detect all possible non-deterministic behaviors that
result from such intended underspecification of evaluation strategies.  We will
learn how to do that when we define the IMP language later in this tutorial;
we will also learn how to enforce a particular order of evaluation.

In order for the above strictness declaration to work effectively and
efficiently, we need to tell the K tool which expressions are meant to be
results of computations, so that it will not attempt to evaluate them anymore.
One way to do it is to make `Val` a syntactic subcategory of the builtin
`KResult` syntactic category.  Since we use the same K parser to also parse
the semantics, we use the same `syntax` keyword to define additional syntax
needed exclusively for the semantics (like `KResult`s).  See `lambda.k`.

Compile again and then run some programs.  They should all work as expected.
In particular, `free-variable-capture.lambda` now evaluates to `a y`.

We now got a complete and working semantic definition of call-by-value
lambda-calculus.  While theoretically correct, our definition is not
easy to use and disseminate.  In the next lessons we will learn how to
generate formatted documentation for LAMBDA and how to extend LAMBDA
in order to write human readable and interesting programs.
