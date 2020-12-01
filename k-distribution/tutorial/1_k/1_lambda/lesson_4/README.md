<!-- Copyright (c) 2012-2019 K Team. All Rights Reserved. -->

# Generating Documentation; Latex Attributes

In this lesson we learn how to generate formatted documentation from K
language definitions.  We also learn how to use Latex attributes to control
the formatting of language constructs, particularly of ones which have a
mathematical flavor and we want to display accordingly.

To enhance readability, we may want to replace the keyword `lambda` by the
mathematical lambda symbol in the generated documentation.  We can control
the way we display language constructs in the generated documentation
by associating them Latex attributes.

This is actually quite easy.  All we have to do is to associate a `latex`
attribute to the production defining the construct in question, following
the Latex syntax for defining new commands (or macros).

In our case, we associate the attribute `latex(\lambda{#1}.{#2})` to the
production declaring the lambda abstraction (recall that in Latex, `#n` refers
to the n-th argument of the defined new command).

Now, when you call `krun`, you can add the `--output latex` option to get a
Latex AST of the output term. This option also works for `kast` and `kprove`.

We will later see, in Lesson 9, that we can add arbitrarily complex Latex
comments and headers to our language definitions, which give us maximum
flexibility in formatting our language definitions.

Now we have a simple programming language, with a nice documentation.  However,
it is not easy to write interesting programs in this language.  Almost all
programming languages build upon existing data-types and libraries.  The K
tool provides a few of these (and you can add more).

In the next lesson we show how we can add builtin integers and Booleans to
LAMBDA, so we can start to evaluate meaningful expressions.

Go to [Lesson 5, LAMBDA: Adding Builtins; Side Conditions](../lesson_5/README.md).

[MOVIE (out of date) [3'13"]](http://youtu.be/ULXA4e_6-DY)
