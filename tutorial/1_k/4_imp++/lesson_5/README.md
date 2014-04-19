<!-- Copyright (c) 2010-2014 K Team. All Rights Reserved. -->

### Deleting, Saving and Restoring Cell Contents

In this lesson we will see how easily we can delete, save and/or restore
contents of cells in order to achieve the desired semantics of language
constructs that involve abrupt changes of control or environments.  We have
seen similar or related K features in the LAMBDA++ language in Part 3 of the tutorial.

Let us start by adding semantics to the `halt` statement.  As its name says,
what we want is to abruptly terminate the execution of the program.  Moreover,
we want the program configuration to look as if the program terminated
normally, with an empty computation cell.  The simplest way to achieve that is
to simply empty the computation cell when `halt` is encountered:

    rule <k> halt; ~> _ => . </k>

It is important to mention the entire `<k/>` cell here, with both its membranes
closed, to make sure that its entire contents is discarded.  Note the
anonymous variable, which matches the rest of the computation.

`kompile` and `krun` `sum-io.imp`.  Note that unlike in Lesson 4, the program
terminates with an empty computation cell now.

As mentioned earlier, the semantics of blocks that was inherited from IMP is
wrong.  Program `locals.imp` shows it very clearly: the environments are not
correctly restored at block exits.  One way to fix the problem is to take
a snapshot of the current environment when a block is entered and save it
somewhere, and then to restore it when the block is left.  There are many
ways to do this, which you can explore on your own: for example you can add
a new list cell for this task where to push/pop the environment snapshots in
a stack style; or you can use the existing environment cell for this purpose,
but then you need to change the variable access rules to search through the
stacked environments for their variable.

My preferred solution is to follow a style similar to how we saved/restored
LAMBDA++ environments in Part 3 of the Tutorial, namely to use the already
existing `<k/>` cell for such operations.  More specifically, we place a
*reminder* item in the computation whenever we need to take a snapshot of
some cell contents; the item simply consists of the entire contents of the cell.
Then, when the reminder item is reached, we restore the contents of the cell:

    rule <k> {S} => S ~> Rho ...</k> <env> Rho </env>  [structural]

The only thing left now is to give the definition of environment restore:

    rule <k> Rho => . ...</k> <env> _ => Rho </env>    [structural]

Done.  `kompile` and `krun` `locals.imp`.  Everything should work correctly now.
Note that the rule above is different from the one we had for LAMBDA++ in
Part 3 of the tutorial, in that here there is no value preceding the environment
restoration item in the computation; that's because IMP++ statements,
unlike LAMBDA++'s expressions, evaluate to nothing (`.`).

In the next lesson we will give semantics to the `spawn S` construct, which
dynamically creates a concurrent shared-memory thread executing statement `S`.
