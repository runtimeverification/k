<!-- Copyright (c) 2010-2014 K Team. All Rights Reserved. -->

### Extending/Changing an Existing Language Syntax

Here we learn how to extend the syntax of an existing language, both with
new syntactic constructs and with more general uses of existing constructs.
The latter, in particular, requires changes of the existing semantics.

Consider the IMP language, as defined in Lesson 4 of Part 2 of the tutorial.

Let us first add the new syntactic constructs, with their precedences:

- variable increment, `++`, which increments an integer variable and
evaluates to the new value;
- `read`, which reads and evaluates to a new integer from the input buffer;
- `print`, which takes a comma-separated list of arithmetic expressions,
  evaluates all of them, and then prints their values to the output buffer;
  we therefore define a new list syntactic category, `AExps`, which we pass
  as an argument to print; moreover, we declare print `strict`, to evaluate
  its `AExps`-list argument, and then the `AExps` list construct `seqstrict`,
  so lists of arithmetic expressions get evaluated from left-to-right whenever
  they reach the top of the `<k/>` cell (replace `seqstrict` with `strict`
  if you want expressions in a list to evaluate non-deterministically and
  interleaved); we also go ahead and add strings as arithmetic expressions,
  because we intend print to also take strings, in order to print nice
  messages to the user;
- `halt`, which abruptly terminates the program; and
- `spawn`, which takes a statement and creates a new concurrent thread
  executing it and sharing its environment with the parent thread.

Also, we want to allow local variable declarations, which can appear anywhere
a statement can appear.  Their scope ranges from the place they are defined
until the end of the current block, and they can shadow previous declarations,
both inside and outside the current block.  The simplest way to define the 
syntax of the new variable declarations is as ordinary statements, at the same
time removing the previous `Pgm` syntactic category and its construct.
Programs are now just statements.

We are now done with adding the new syntax and modifying the old one.
Note that the old syntax was modified in a way which makes the previous IMP
programs still parse, but this time as statements.  Let us then modify
the configuration variable `$PGM` to have the sort `Stmt` instead of `Pgm`,
and let us try to run the old IMP programs, for example `sum.imp`.

Note that they actually get stuck with the *global* declaration on the top
of their computations.  This is because variable declarations are now treated
like any statements, in particular, the sequential composition rule applies.
This makes the old IMP rule for global variable declarations not match anymore.
We can easily fix it by replacing the anonymous variable `_`, which matched
the program's statement that now turned into the remaining computation in
the `<k/>` cell, with the cell frame variable `...`, which matches the
remaining computation.  Similarly, we have to change the rule for the case
where there are no variables left to declare into one that dissolves itself.

We can now run all the previous IMP programs, in spite of the fact that
our IMP++ semantics is incomplete and, more interestingly, in spite of the
fact that our current semantics of blocks is incorrect in what regards the
semantics of local variable declarations (note that the old IMP programs do
not declare block-local variables, which is why they still run correctly).

Let us also write some proper IMP++ programs, which we would like to execute
once we give semantics to the new constructs.

`div.imp` is a program manifesting non-deterministic behaviors due to the
desired non-deterministic evaluation strategy of division and the fact that
expressions will have side effects once we add variable increment.  We will
be able to see all the different behaviors of this program.  Challenge: can
you identify the behavior where the program performs a division-by-zero?

If we run `div.imp` now, it will get stuck with the variable increment
construct on top of the computation cell.  Once we give it a semantics, in
the next lesson, `div.imp` will execute completely (all the other constructs
in `div.imp` already have their semantics defined as part of IMP).

Note that some people prefer to define all their semantics in a *by need*
style, that is, they first write and parse lots of programs, and then they
add semantics to each language construct on which any of the programs gets
stuck, and so on and so forth until they can run all the programs.

`io.imp` is a program which exercises the input/output capabilities of the
language: reads two integers and prints three strings and an integer.
Note that the variable declaration is not the first statement anymore.

`sum-io.imp` is an interactive variant of the sum program.

`spawn.imp` is a program which dynamically creates two threads that interact
with the main thread via the shared variable x.  Lots of behaviors will be
seen here once we give spawn the right semantics.

Finally, `locals.imp` tests whether variable shadowing/unshadowing works well.

In the next lesson we will prepare the configuration for the new constructs,
and will see what it takes to adapt the semantics to the new configuration.
Specifically, we will split the state cell into an environment cell and a
store cell, like in LAMBDA++ in Part 3 of the tutorial.
