<!-- Copyright (c) 2010-2019 K Team. All Rights Reserved. -->

### Tagging; Transition Kompilation Option

In this lesson we add the semantics of variable increment.  In doing so, we
learn how to tag syntactic constructs and rules and then use such tags to
instruct the `kompile` tool to generate the desired language model that is
amenable for exhaustive analysis.

The variable increment rule is self-explanatory:

    rule <k> ++X => I +Int 1 ...</k>
         <env>... X |-> N ...</env>
         <store>... N |-> (I => I +Int 1) ...</store>

We can now run programs like our `div.imp` program introduced in Lesson 1.
Do it.

The addition of increment makes the evaluation of expressions have side
effects.  That, in combination with the non-determinism allowed by the
strictness attributes in how expression constructs evaluate their
arguments, makes expressions in particular and programs in general have
non-deterministic behaviors.  One possible execution of the `div.imp` program
assigns `1` to `y`'s location, for example, but this program manifests several
other behaviors, too.

To see all the (final-state) behaviors that a program can have, you can call
the `krun` tool with the option `--search`.  For example:

    krun div.imp --search

Oops, we see only one solution, the same as when we ran it without search.

Here is what happens.  `krun` can only explore as much of the transition
system associated to a program as `kompile` allowed the generated language
model to yield.  Since most of the K users are interested in language models
that execute efficiently, that is, in faster interpreters for the defined
languages, by default `kompile` optimizes the generated language model for
execution.  In particular, it inserts no backtracking markers, which `krun`
uses when called with the `--search` option in order to systematically generate
the entire transition system associated to a program.  This is why `krun`
showed us only one solution when run with the `--search` option on `div.imp`.

We next explain how to tell `kompile` what kind of language model we are
interested in for analysis purposes.  When you experiment with non-determinism
in a language semantics, you should keep it in mind that the `--transition`
option of `kompile` allows you to configure what counts as a transition in
your language model.  We here only discuss transitions due to the
non-deterministic evaluation strategies of language constructs, but we will
see in future lectures (see Lesson 6 of IMP++, where we add concurrency) that
we can also have transitions due to non-deterministic applications of rewrite
rules.

If you want to explore the entire behavior space due to non-deterministic
evaluation strategies, then you should include all the language constructs 
in the `--transition` option.  This may sound like the obvious thing to
always do, but as soon as you do it you soon realize that it is way too much
in practice when you deal with large languages or programs.  There are simply
too many program behaviors to consider, and `krun` will likely hang
on you or crush.  For example, a small ten-statement program where each
statement uses one strict expression construct already has 1000+ behaviors for
`krun` to explore!  Driven by practical needs of its users, the K tool
therefore allows you to finely tune the generated language models using the
`--transition` option.

To state which constructs are to be considered to generate transitions in the
generated language model, and for other reasons, too, the K tool allows you to
tag any production and any rule.  You can do this the same way we tagged
rules with the `structural` keyword in earlier tutorials: put the tag in
brackets.  You can associate multiple tags to the same construct or rule, and
more than one construct or rule can have the same tag.  As an example, let us
tag the division construct with `division`, the lookup rule with `lookup` and
the increment rule with `increment`.  The tags of the rules are not needed
in this lesson, we do it only to demonstrate that rules can also be tagged.

The least intrusive way to enforce our current language to explore the
entire space of behaviors due to the strictness of division is to `kompile` it
with the following option:

    kompile imp.k --transition "division"

It is interesting to note that the `lookup` and `increment` rules are the only
two rules which can trigger non-deterministic behaviors for division, because
no other rule but these two can ever apply while a division operation is
heated.  Previous versions of K allowed you to also specify which rules could
trigger non-deterministic behaviors of operator evaluation strategies,
but that option was rarely used and is not available anymore.

Note that it is highly non-trivial to say precisely whether a strict language
construct may yield non-deterministic behaviors.  For example, division's
strictness would yield no non-determinism if the language had no side effects.
It is even harder to say so for a particular program.  Consequently, our K
implementation makes no attempt to automatically detect which operations
should be tagged as transitions.  Instead, it provides the functionality to
let you decide it.

Now the command

    krun div.imp --search

shows us all five behaviors of this program.  Interestingly, one
of the five behaviors yields a division by zero!

The `--transition` option can be quite useful when you experiment with your
language designs or when you formally analyze programs for certain kinds of
errors.  Please let us know if you ever need more finer-grained control over
the non-determinism of your language models.

Before we conclude this lesson, we'd like to let you know one trick, which
you will hopefully not overuse: you can tag elements in your K definition with
`kompile` option names, and those elements will be automatically included in
their corresponding options.  For example, if you tag the division production
with `transition` then the command 

    kompile imp

is completely equivalent to the previous `kompile` command.

Please use this default behavior with caution, or even better, try to avoid
using it!  You may be tempted to add the `transition` tag to lots of elements
and then forget about them; your language models will then be increasingly slower
when you execute them and you may wonder why ...  This convention is typically
convenient when you want to quickly experiment with non-determinism and do not
want to bother inventing tag names and calling `kompile` with options.

In the next lesson we add input/output to our language and learn how to
generate a model of it which behaves like an interactive interpreter!
