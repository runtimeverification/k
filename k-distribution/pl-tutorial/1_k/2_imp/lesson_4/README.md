---
copyright: Copyright (c) Runtime Verification, Inc. All Rights Reserved.
---

# Configuration Abstraction, Part 1; Types of Rules

Here we will complete the K definition of IMP and, while doing so, we will
learn the very first step of what we call _configuration abstraction_.

## The IMP Semantic Rules

Let us add the remaining rules, in the order in which the language constructs
were defined in IMP-SYNTAX.

The rules for the arithmetic and Boolean constructs are self-explanatory.
Note, however, that K will infer the correct sorts of all the variables in
these rules, because they appear as arguments of the builtin operations
(`_+Int_`, etc.). Moreover, the inferred sorts will be enforced dynamically.
Indeed, we do not want to apply the rule for addition, for example, when the
two arguments are not integers. In the rules for `&&`, although we prefer to
not do it here for simplicity, we could have eliminated the dynamic check by
replacing `B` (and similarly for `_`) with `B:K`. Indeed, it can be shown
that whenever any of these rules apply, `B` (or `_`) is a `BExp` anyway.
That's because there is no rule that can touch such a `B` (or `_`); this
will become clearer shortly, when we discuss the first step of configuration
abstraction. Therefore, since we know that `B` will be a `BExp` anyway, we
could save the time it takes to check its sort; such times may look minor,
but they accumulate, so some designers may prefer to avoid run-time checks
whenever possible.

The block rules are trivial. However, the rule for non-empty blocks is
semantically correct only because we do not have local variable declarations
in IMP. We will have to change this rule in IMP++.

The assignment rule has two `=>`: one in the `k` cell dissolving the
assignment statement, and the other in the `state` cell updating the value of
the assigned variable. Note that the one in the `state` is surrounded by
parentheses: `(_ => I)`. That is because `=>` is greedy: it matches as much
as it can to the left and to the right, until it reaches the cell boundaries
(closed or open). If you want to limit its scope, or for clarity, you can use
parentheses like here.

The rule for sequential composition simply desugars `S1 S2` into `S1 ~> S2`.
Indeed, the two have exactly the same semantics. Note that statements
_evaluate_ to nothing (`.`), so once `S1` is processed in `S1 ~> S2`, then the
next task is automatically `S2`, without wasting any step for the transition.

The rules for the conditional and while statements are clear. One thing to
keep in mind now is that the `while` unrolling rule will not apply
indefinitely in the positive branch of the resulting conditional, because
of K's configuration abstraction, which will be discussed shortly.

An IMP program declares a set of variables and then executes a
statement in the state obtained after initializing all those variables
to `0`. The rules for programs initialize the declared variables one by one,
checking also that there are no duplicates. We check for duplicates only for
demonstration purposes, to illustrate the `keys` predefined operation that
returns the set of keys of a map, and the set membership operation `in`.
In practice, we typically define a static type checker for our language,
which we execute before the semantics and reject inappropriate programs.

The use of the `.Ids` in the second rule is not necessary. We could have
written `int; S` instead of `int .Ids; S` and the K tool would parse it and
kompile the definition correctly, because it uses the same parser used for
parsing programs also to parse the semantics. However, we typically prefer to
explicitly write the _nothing_ values in the semantics, for clarity;
the parser has been extended to accept these. Note that the first rule
matches the entire `k` cell, because `int_;_` is the top-level program
construct in IMP, so there is nothing following it in the computation cell.
The anonymous variable stands for the second argument of this top-level program
construct, not for the rest of the computation. The second rule could have
also been put in a complete `k` cell, but we preferred not to, for simplicity.

Our IMP semantics is now complete, but there are a few more things that we
need to understand and do.

## Configuration Abstraction, Part 1

First, let us briefly discuss the very first step of configuration abstraction.
In K, all semantic rules are in fact rules between configurations. As soon
explained in the IMP++ tutorial, the declared configuration cell structure is
used to automatically complete the missing configuration parts in rules.
However, many rules do not involve any cells, being rules between syntactic
terms (of sort `K`); for example, we had only three rules involving cells in our
IMP semantics. In this case, the `k` cell will be added automatically and the
actual rewrite will happen on top of the enclosed computation. For example,
the rule for the `while` loop is automatically translated into the following:

    rule <k> while (B) S => if (B) {S while (B) S} else {} ...</k>

Since the first task in computations is what needs to be done next, the
intuition for this rule completion is that the syntactic transition
only happens when the term to rewrite is ready for processing. This explains,
for example, why the while loop unrolling does not indefinitely apply in the
positive branch of the conditional: the inner while loop is not ready for
evaluation yet. We call this rule completion process, as well as other
similar ones, _configuration abstraction_. That is because the incomplete
rule abstracts away the configuration structure, thus being easier to read.
As seen soon when we define IMP++, configuration abstraction is not only a
user convenience; it actually significantly increases the modularity of our
definitions. The k-cell-completion is only the very first step, though.

If you really want certain rewrites over syntactic terms to apply
anywhere they match, then you should tag the rule with the attribute
`anywhere`, which was discussed in Tutorial 1, Lesson 2.5.

Kompile and then krun the programs that you only parsed in Lesson 1. They
should all execute as expected. The state cell shows the final state
of the program. The `k` cell shows the final code contents, which should be
empty whenever the IMP program executes correctly.

Kompile also with the documentation option and take a look at the generated
documentation. The assignment rule should particularly be of interest,
because it contains two local rewrites.

In the next lesson we comment the IMP definition and conclude this tutorial.

Go to [Lesson 5, IMP: Completing and Documenting IMP](../lesson_5/README.md).

[MOVIE (out of date) [09'16"]](https://youtu.be/fR2VEfGHtho)
