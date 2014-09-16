<!-- Copyright (c) 2010-2014 K Team. All Rights Reserved. -->

### Everything Changes: Syntax, Configuration, Semantics

In this lesson we add thread joining, one of the simplest thread
synchronization mechanisms.  In doing so, we need to add unique ids
to threads in the configuration, and to modify the syntax to allow `spawn`
to return the id of the newly created thread.  This gives us an opportunity
to make several other small syntactic and semantics changes to the language,
which make it more powerful or more compact at a rather low cost.

Before we start, let us first copy and modify the previous `spawn.imp` program
from Lesson 1 to make use of thread joining.  Recall from Lesson 6 that in some
runs of this program the main thread completed before the child threads,
printing a possibly undesired value of `x`.  What we want now is to assign
unique ids to the two spawned threads, and then to modify the main thread to
join the two child threads before printing.  To avoid adding a new type to
the language, let's assume that thread ids are integer numbers.  So we declare
two integers, `t1` and `t2`, and assign them the two spawn commands.  In order
for this to parse, we will have to change the syntax of spawn to be an
arithmetic expression construct instead of a statement.  Once we do that,
we have a slight syntactic annoyance: we need to put two consecutive `;`
after the spawn assignment, one for the assignment statement inside the spawn,
and another for the outer assignment.  To avoid the two consecutive semicolons,
we can syntactically enforce spawn to take a block as argument, instead of a
statement.  Now it looks better.  The new `spawn.imp` program is still
non-deterministic, because the two threads can execute in any order and even
continue to have a data-race on the shared variable `x`, but we should see fewer
behaviors when we use the `join` statements.  If we want to fully synchronize
this program, we can have the second thread start with a `join(t1)` statement.
Then we should only see one behavior for this program.

Let us now modify the language semantics.  First, we move the `spawn`
construct from statements to expressions, and make it take a block.
Second, we add one more sub-cell to the thread cell in the configuration,
`<id/>`, to hold the unique identifier of the thread.  We want the main
thread to have id `0`, so we initialize this cell with `0`.  Third, we modify
the spawn rule to generate a fresh integer identifier, which is put in the
`<id/>` cell of the child thread and returned as a result of `spawn` in the
parent thread.  Fourth, let us add the `join` statement to the language,
both syntactically and semantically.  So in order for the `join(T)` statement
to execute, thread `T` must have its computation empty.  However, in order
for this to work we have to get rid of the thread termination cleanup rule.
Indeed, we need to store somewhere the information that thread `T` terminated;
the simplest way to do it is to not remove the terminated threads.  Feel free
to experiment with other possibilities, too, here.  For example, you may add
another cell, `<done/>`, in which you can store all the thread ids of the
terminated and garbage-collected threads.

Let us now `kompile imp.k` and convince ourselves that the new `spawn.imp`
with `join` statements indeed has fewer behaviors than its variant without
`join` statements.  Also, let us convince ourselves that the fully synchronized
variant of it indeed has only one behavior.

Note that now spawn, like variable increment, makes the evaluation of
expressions to have side effects.  Many programming languages in fact allow
expressions to be evaluated only for their side effects, and not for their
value.  This is typically done by simply adding a `;` after the expression
and thus turning it into a statement.  For example, `++x;`.  Let as also
allow arithmetic expressions in our language to be used as statements, by
simply adding the production `AExp ";"` to `Stmt`, with evaluation strategy
`strict` and with the expected semantics discarding the value of the `AExp`.

Another simple change in syntax and semantics which gives our language more
power, is to remove the `;` from the syntax of variable assignments and to make
them expression instead of statement constructs.  This change, combined with
the previous one, will still allow us to parse all the programs that we could
parse before, but will also allow us to parse more programs.  For example, we
can now do sequence assignments like in C: `x = y = z = 0`.  The semantics
of assignment now has to return the assigned value also to the computation,
because we want the assignment expression to evaluate to the assigned value.

Let us also make another change, but this time one which only makes the
definition more compact.  Instead of defining statement sequential
composition as a binary construct for statements, let us define a new
syntactic construct, `Stmts`, as whitespace-separated lists of `Stmt`.  This
allows us to get rid of the empty blocks, because we can change the syntax of
blocks to `{Stmts}` and `Stmts` also allows the empty sequence of statements.
However, we do have to make sure that `.Stmts` dissolves.

In general, unless you are defining a well-established programming language,
it is quite likely that your definitions will suffer lots of changes like the
ones seen in this lecture.  You add a new construct, which suggests changes
in the existing syntax making in fact your language parse more programs,
which then requires corresponding changes in the semantics, and so on.
Also, compact definitions are desirable in general, because they are easier
to read and easier to change if needed later.

In the next lesson we wrap up and document the definition of IMP++.
