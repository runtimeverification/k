---
copyright: Copyright (c) Runtime Verification, Inc. All Rights Reserved.
---

# Tagging; Transition Kompilation Option

In this lesson we add the semantics of variable increment. In doing so, we
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
effects. That, in combination with the non-determinism allowed by the
strictness attributes in how expression constructs evaluate their
arguments, makes expressions in particular and programs in general have
non-deterministic behaviors. One possible execution of the `div.imp` program
assigns `1` to `y`'s location, for example, but this program manifests several
other behaviors, too.

To see all the (final-state) behaviors that a program can have, you can call
the `krun` tool with the option `--search`. For example:

    krun div.imp --search

In the next lesson we add input/output to our language and learn how to
generate a model of it which behaves like an interactive interpreter!

Go to [Lesson 4, IMP++: Semantic Lists; Input/Output Streaming](../lesson_4/README.md).

[MOVIE (out of date) [06'56"]](https://youtu.be/uwCUfWt7n-o)
