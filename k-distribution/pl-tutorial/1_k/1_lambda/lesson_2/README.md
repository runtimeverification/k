---
copyright: Copyright (c) Runtime Verification, Inc. All Rights Reserved.
---

# Module Importing, Rules, Variables

We here learn how to include a predefined module (SUBSTITUTION), how to
use it to define a K rule (the characteristic rule of lambda calculus),
and how to make proper use of variables in rules.

Let us continue our `lambda.k` definition started in the previous lesson.

The `requires` keyword takes a `.k` file containing language features that
are needed for the current definition, which can be found in the
[k-distribution/include/kframework/builtin](../../../../include/kframework/builtin/README.md) folder.  Thus, the command

    require "substitution.k"

says that the subsequent definition of LAMBDA needs the generic substitution,
which is predefined in file `substitution.k` under the folder
[k-distribution/include/kframework/builtin](../../../../include/kframework/builtin/README.md).  Note that substitution can be defined itself in K,
although it uses advanced features that we have not discussed yet in this
tutorial, so it may not be easy to understand now.

Using the `imports` keyword, we can now modify LAMBDA to import the module
SUBSTITUTION, which is defined in the required `substitution.k` file.

Now we have all the substitution machinery available for our definition.
However, since our substitution is generic, it cannot know which language
constructs bind variables, and what counts as a variable; however, this
information is critical in order to correctly solve the variable capture
problem.  Thus, you have to tell the substitution that your lambda construct
is meant to be a binder, and that your `Id` terms should be treated as variables
for substitution.  The former is done using the attribute `binder`.
By default, `binder` binds all the variables occurring anywhere in the first 
argument of the corresponding syntactic construct within its other arguments;
you can configure which arguments are bound where, but that will be discussed
in subsequent lectures.  To tell K which terms are meant to act as variables
for binding and substitution, we have to explicitly subsort the desired syntactic 
categories to the builtin `KVariable` sort.

Now we are ready to define our first K rule.  Rules are introduced with the
keyword `rule` and make use of the rewrite symbol, `=>`.  In our case,
the rule defines the so-called lambda calculus *beta-reduction*, which
makes use of substitution in its right-hand side, as shown in `lambda.k`.

By convention, variables that appear in rules start with a capital letter
(the current implementation of the K tool may even enforce that).

Variables may be explicitly tagged with their syntactic category (also called
*sort*).  If tagged, the matching term will be checked at run-time for
membership to the claimed sort.  If not tagged, then no check will be made.
The former is safer, but involves the generation of a side condition to the
rule, so the resulting definition may execute slightly slower overall.

In our rule in `lambda.k` we tagged all variables with their sorts, so we chose
the safest path.  Only the `V` variable really needs to be tagged there,
because we can prove (using other means, not the K tool, as the K tool is not
yet concerned with proving) that the first two variables will always have the
claimed sorts whenever we execute any expression that parses within our
original grammar.

Let us compile the definition and then run some programs.  For example,

    krun closed-variable-capture.lambda

yields the output

    <k>
      lambda y . ((lambda x . (lambda y . (x  y))) y)
    </k> 

Notice that only certain programs reduce (some even yield non-termination,
such as `omega.lambda`), while others do not.  For example,
`free-variable-capture.lambda` does not reduce its second argument expression
to `y`, as we would expect.  This is because the K rewrite rules between syntactic
terms do not apply anywhere they match.  They only apply where they have been
given permission to apply by means of appropriate evaluation strategies of language
constructs, which is done using strictness attributes, evaluation contexts,
heating/cooling rules, etc., as discussed in the next lessons.

The next lesson will show how to add LAMBDA the desired evaluation strategies
using strictness attributes.

Go to [Lesson 3, LAMBDA: Evaluation Strategies using Strictness](../lesson_3/README.md)

[MOVIE (out of date) [4'03"]](https://youtu.be/NDXgYfHG6R4)
