### Reusing Existing Semantics

[MOVIE [3'21"]](http://youtu.be/tW4KRdgBIGo)

In this lesson we will learn that, in some cases, we can reuse existing
semantics of language features without having to make any change!

Although the definitional style of the basic LAMBDA language changed quite
radically in our previous lesson, compared to its original definition in
Part 1 of the tutorial, we fortunately can reuse a large portion of the previous
definition.  For example, let us just cut-and-paste the rest of the definition
from Lesson 7 in Part 1 of the tutorial.

Let us `kompile` and `krun` all the remaining programs from Part 1 of the tutorial.
Everything should work fine, although the store contains lots of garbage.
Garbage collection is an interesting topic, but we do not do it here.
Nevertheless, much of this garbage is caused by the intricate use of the
fixed-point combinator to define recursion.  In a future lesson in this tutorial
we will see that a different, environment-based definition of fixed-points will
allocate much less memory.

One interesting question at this stage is: how do we know when we can reuse
an existing semantics of a language feature?  Well, I'm afraid the answer is:
we don't.  In the next lesson we will learn how reuse can fail for quite subtle
reasons, which are impossible to detect statically (and some non-experts may
fail to even detect them at all).
