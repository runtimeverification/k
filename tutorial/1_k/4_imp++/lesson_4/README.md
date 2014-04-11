<!-- Copyright (C) 2010-2014 K Team. All Rights Reserved. -->

### Semantic Lists; Input/Output Streaming

In this lesson we add semantics to the read and print IMP++ constructs.
In doing so, we also learn how to use semantic lists and how to connect
cells holding semantic lists to the standard input and standard output.
This allows us to turn the K semantics into an interactive interpreter.

We start by adding two new cells to the configuration,

    <in color="magenta"> .List </in>
    <out color="Orchid"> .List </out>

each holding a semantic list, initially empty.  Semantic lists are
space-separated sequences of items, each item being a term of the form
`ListItem(t)`, where `t` is a term of sort `K`.  Recall that the semantic maps,
which we use for states, environments, stores, etc., are sets of pairs
`t1 |-> t2`, where `t1` and `t2` are terms of sort K.  The `ListItem` wrapper
is currently needed, to avoid parsing ambiguities.

Since we want the print statement to also print strings, we need to tell
K that strings are results.  To make it more interesting, let us also overload
the `+` symbol on arithmetic expressions to also take strings and, as a
result, to concatenate them.  Since `+` is already strict, we only need to add
a rule reducing the IMP addition of strings to the builtin operation `+String`
which concatenates two strings.

Let us next give semantics to read and print.  The former reads and consumes
the first integer item from the `<in/>` cell; note that our read only reads
integer values (it gets stuck if the first item in the `<in/>` cell is not an
integer).  The latter takes each of print's arguments in order and places
them at the end of the `<out/>` cell.  Since we want to print both integers and
string values, to avoid writing two rules, one for each type of value, we
instead add a new syntactic category, `Printable`, which is the union of
integers and strings.  Note that there is no need to also add syntactic lists
of `Printable` elements, because we can use a variable over syntactic lists of
arithmetic expressions to match the remaining arguments of print (in other
words, we can output the first argument of the print statement as soon as it
becomes a `Printable`, even if the remaining arguments are not evaluated yet).

Let us `kompile` and `krun` the `io.imp` program discussed in Lesson 1.  As
expected, it gets stuck with a read construct on top of the computation and
with an empty `<in/>` cell.  To run it, we need to provide some items in the
`<in/>` cell, so that the rule of read can match.  Let us add 

    <in> ListItem(3) ListItem(5) ListItem(7) </in>

Now, if we `krun` `io.imp`, we can see that its execution completes normally
(the `<k/>` cell is empty), that the first two items have been removed by the
two read constructs from the `<in/>` cell, and that the desired strings and
numbers have been placed into the `<out/>` cell.

Cells holding semantic lists can be connected to the standard input and
standard output buffers, and `krun` knows how to handle these appropriately.
Let us connect the `<in/>` cell to the standard input using the cell attribute
`stream="stdin"` and the `<out/>` cell to the standard output with the
attribute `stream="sdtout"`.  A cell connected to the standard input will
take its items from the standard input and block the rewriting process when
an input is needed until an item is available in the standard input buffer.
A cell connected to the standard output buffer will send all its items, in
order, to the standard output.

Let us `kompile` and `krun` `io.imp` again.  It prints the message and then
waits for your input numbers.  Type in two numbers, then press `<Enter>`.
A message with their sum is then printed, followed by the final configuration.
If you do not want to see the final configuration, and thus obtain a realistic
interpreter for our language, then call `krun` with the option `--no-config`:

    krun io.imp --no-config

Let us now `krun` our interactive sum program, which continuously reads numbers
from the console and prints the sum of numbers up to them:

    krun sum-io.imp

Try a few numbers, then `0`.  Note that the program terminated, but with junk
in the `<k/>` cell, essentially with a `halt` statement on its top.  Of course,
because `halt` has been reached and it has no semantics yet.

In the next lesson we give the semantics of `halt` and also fix the semantics
of blocks with local variable declarations.
