<!-- Copyright (c) 2010-2014 K Team. All Rights Reserved. -->

## Part 4: Defining IMP++

IMP++ extends IMP, which was discussed in Part 2 of this tutorial, with several
new syntactic constructs.  Also, some existing syntax is generalized, which
requires non-modular changes of the existing IMP semantics.  For example,
global variable declarations become local declarations and can occur
anywhere a statement can occur.  In this tutorial we will learn the following:

* That (and how) existing syntax/semantics may change as a language evolves.
* How to refine configurations as a language evolves.
* How to define and use fresh elements of desired sorts.
* How to tag syntactic constructs and rules, and how to use such tags
  with the `superheat`/`supercool`/`transition` options of `kompile`.
* How the `search` option of `krun` works.
* How to stream cells holding semantic lists to the standard input/output,
  and thus obtain interactive interpreters for the defined languages.
* How to delete, save and restore cell contents.
* How to add/delete cells dynamically.
* More details on how the configuration abstraction mechanism works.

Like in the previous tutorials, this folder contains several lessons, each
adding new features to IMP++.  Do them in order and make sure you completed
and understood the previous tutorials.
