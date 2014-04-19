<!-- Copyright (c) 2010-2014 K Team. All Rights Reserved. -->

### Tagging; Superheat/Supercool Kompilation Options

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

We next explain how to tell `kompile` in what kind of language model we are
interested for analysis purposes.  When we experiment with non-determinism due
to evaluation strategies of language constructs, we should keep in mind that
`kompile` allows us to configure two important parameters, called
`--superheat`, and respectively, `--supercool`:

1. `superheat`: what language constructs we want the generated language model
to allow for exhaustive non-deterministic analysis; and
2. `supercool`: what rules we want to trigger the search for a *next behavior*.

If you want to explore the entire behavior space due to non-deterministic
evaluation strategies, then you should include all the language constructs 
in the `--superheat` option and all the rules in the `--supercool` option.
This may sound to a K beginner like the obvious thing to always do, but trust
us, it is way too much in practice when you deal with large languages!  There
are simply too many behaviors for `krun` to consider, and it will likely hang
on you or crush.  For example, a small ten-statement program where each
statement uses one strict expression construct already has 1000+ behaviors for
`krun` to explore!  Driven by practical needs of its users, the K tool
therefore allows you to finely tune the generated language models using the
two options above.  Metaphorically, the `super` prefix is meant to fully
incorporate in the generated language model the theoretical meaning of the
corresponding operation: `superheat` indicates strict language constructs
whose heating rules have to be considered as backtracking markers for search,
and `supercool` indicates rules which enforce the application of the
corresponding cooling rules of those constructs.

To state which constructs are `superheat` and which rules are `supercool`, and
not only for these reasons, the K tool allows you to tag any productions
and any rules.  You can do this the same way we tagged rules with the
`structural` keyword in earlier tutorials: put the tag in brackets.  You can
associate multiple tags to the same construct or rule, and more than one
construct or rule can have the same tag.  As an example, let us tag the
division construct with `division`, the lookup rule with `lookup` and
the increment rule with `increment`.

The least intrusive way to enforce our current language to explore the
entire non-determinism due to the strictness of division, is to `kompile` it
with the following options:

    kompile imp.k --superheat="division" --supercool="lookup increment"

In other words, we want to explore the non-determinism due only to the
heating rules corresponding to the division construct, and we want to search
for new behaviors to be triggered only by the lookup and increment rules.
Note that, indeed, no other rule but these two can ever apply while a division
operation is heated.

Now the command

    krun div.imp --search

shows us all five behaviors of this program.  Interestingly, one
of the five behaviors yields a division by zero!

It will take you a little to master the use of these `super` options, but
they can be quite useful when you experiment with your language designs or
when you formally analyze programs for certain kinds of errors.  Please let
us know if you ever need even finer-grained control over the non-determinism
of your language models.

Before we conclude this lesson, we'd like to let you know one trick, which
you will hopefully not overuse: you can tag things in your K definition with
`kompile` option names, and those things will be automatically included in
their corresponding options.  For example, if you tag the division production
with `superheat` and the lookup and increment rules with `supercool`, then 
the command 

    kompile imp

is completely equivalent to the previous `kompile` command!

Please use this default behavior with caution, or even better, try to avoid
using it!  You may be tempted to add the `superheat` and `supercool` tags to
lots of things and then forget about them; your language models will then be
increasingly slower when you execute them and you may wonder why ...  This
convention is typically convenient when you want to quickly experiment with
non-determinism and do not want to bother inventing tag names and calling
`kompile` with options.

In the next lesson we add input/output to our language and learn how to
generate a model of it which behaves like an interactive interpreter!
