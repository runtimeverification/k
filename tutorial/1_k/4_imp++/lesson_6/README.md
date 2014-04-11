<!-- Copyright (C) 2010-2014 K Team. All Rights Reserved. -->

### Adding/Deleting Cells Dynamically; Configuration Abstraction, Part 2

In this lesson we add dynamic thread creation and termination to IMP, and
while doing so we learn how to define and use configurations whose structure
can evolve dynamically.

Recall that the intended semantics of `spawn S` is to spawn a new concurrent
thread that executes `S`.  The new thread is being passed at creation time
its parent's environment, so it can share with its parent the memory
locations that its parent had access to at creation time.  No other locations
can be shared, and no other memory sharing mechanism is available.
The parent and the child threads can evolve unrestricted, in particular they
can change their environments by declaring new variables or shadowing existing
ones, can create other threads, and so on.

The above suggests that each thread should have its own computation and its
own environment.  This can be elegantly achieved if we group the `<k/>` and
`<env/>` cells in a `<thread/>` cell in the configuration.  Since at any given
moment during the execution of a program there could be zero, one or more
instances of such a `<thread/>` cell in the configuration, it is a good idea
to declare the `<thread/>` cell with multiplicity `*` (i.e., zero, one or more):

    <thread multiplicity="*" color="blue">
      <k color="green"> $PGM:Stmt </k>
      <env color="LightSkyBlue"> .Map </env>
    </thread>

This multiplicity declaration is not necessary, but it is a good idea to do
it for several reasons:

1. it may help the configuration abstraction process,
which may in turn significantly increase the compactness and modularity of
your subsequent rules;
2. it may help various analysis and execution tools,
for example static analyzers to give you error messages when you create cells
where you should not, or K compilers to improve performance by starting
actual concurrent hardware threads or processes corresponding to each cell
instance; and
3. it may help you better understand and control the dynamics
of your configuration, and thus your overall semantics.

For good encapsulation, I (admittedly subjectively) also prefer to put all
thread cells into one cell, `<threads/>`.  This is totally unnecessary here; to
convince yourself that this is indeed true, you can remove this cell once
we are done with the semantics and everything will work without having to
make any changes.

Before we continue, let us `kompile` an `krun` some programs that used to work,
say `sum-io.imp`.  In spite of the relatively radical configuration
reorganization, those programs execute just fine!  How is that possible?
In particular, why do rules like the lookup and assignment still work,
unchanged, in spite of the fact that the `<k/>` and `<env/>` cells are not at the
same level with the `<store/>` cell in the configuration anymore?

Welcome to configuration abstraction, part 2.  Recall that the role of
configuration abstraction is to allow you to only write the relevant
information in each rule, and have the compiler fill-in the obvious and boring
details.  According to the configuration that we declared for our new
language, there is only one reasonable way to complete rules like the lookup,
namely to place the `<k/>` and `</env>` cells inside a `<thread/>` cell, inside a
`<threads/>` cell:

    rule <threads>...
           <thread>...
             <k> X:Id => I ...</k>
             <env>... X |-> N ...</env>
           ...</thread>
         ...<threads/>
         <store>... N |-> I ...</store>  [lookup]

This is the most direct, compact and local way to complete the configuration
context of the lookup rule.  If for some reason you wanted here to match the
`<k/>` cell of one thread and the `<env/>` cell of another thread, then you would
need to explicitly tell K so, by mentioning the two thread cells, for example:

    rule <thread>...
             <k> X:Id => I ...</k>
         ...</thread>
         <thread>...
             <env>... X |-> N ...</env>
         ...</thread>
         <store>... N |-> I ...</store>  [lookup]

By default, K completes rules in a greedy style.  Think this way: what is the
minimal number of changes to my rule to make it fit the declared configuration?
That's what the K tool will do.

Configuration abstraction is technically unnecessary, but once you start
using it and get a feel for how it works, it will become your best friend.
It allows you to focus on the essentials of your semantics, and at the same
time gives you flexibility in changing the configuration later on without
having to touch the rules.  For example, it allows you to remove the
`<threads/>` cell from the configuration, if you don't like it, without
having to touch any rule.

We are now ready to give the semantics of `spawn`:

    rule <k> spawn S => . ...</k> <env> Rho </env>
         (. => <thread>... <k> S </k> <env> Rho </env> ...</thread>)

Note configuration abstraction at work, again.  Taking into account
the declared configuration, and in particular the multiplicity information
`*` in the `<thread/>` cell, the only reasonable way to complete the rule
above is to wrap the `<k/>` and `<env/>` cells on the first line within a
`<thread/>` cell, and to fill-in the `...`s in the child thread with the
default contents of the other subcells in `<thread/>`.  In this case there
are no other cells, so we can get rid of those `...`s, but that would
decrease the modularity of this rule: indeed, we may later on add other
cells within `<thread/>` as the language evolves, for example a function
or an exception stack, etc.

In theory, we should be able to write the rule above even more compactly
and modularly, namely as

    rule <k> spawn S => . ...</k> <env> Rho </env>
         (. => <k> S </k> <env> Rho </env>)

Unfortunately, this currently does not work in the K tool, due to some
known limitations of our current configuration abstraction algorithm.
This latter rule would be more modular, because it would not even depend
on the cell name `thread`.  For example, we may later decide to change
`thread` into `agent`, and we would not have to touch this rule.
We hope this current limitation will be eliminated soon.  

Once a thread terminates, its computation cell becomes empty.  When that
happens, we can go ahead and remove the useless `thread` cell:

    rule <thread>... <k> . </k> ...</thread> => .  [structural]

Let's see what we've got.  `kompile` and `krun` `spawn.imp`.  Note the following:

- The `<threads/>` cell is empty, so all threads terminated normally;
- The value printed is different from the value in the store; the store value
  is not even the one obtained if the threads executed sequentially.

Therefore, interesting behaviors may happen; we would like to see them all!

Based on prior experience with `krun`'s search option, we would hope that

    krun spawn.imp --search

shows all the behaviors.  However, the above does not work, for two reasons.

First, `spawn.imp` is an interactive program, which reads a number from the
standard input.  When analyzing programs exhaustively using the search option,
`krun` has to disable the streaming capabilities (just think about it and you
will realize why).  The best you can do in terms of interactivity with search
is to pipe some input to `krun`: `krun` will flush the standard input buffer
into the cells connected to it when creating the initial configuration (will
do that no matter whether you run it with or without the `--search` option).
For example:

    echo 23 | krun spawn.imp --search

puts `23` in the standard input buffer, which is then transferred in the `<in/>`
cell as a list item, and then the exhaustive search procedure is invoked.

Second, even after piping some input, the `spawn.imp` program still manifests
only one behavior, which does not seem right.  There should be many more.

Like with the `superheat`/`supercool` options discussed in Lesson 3, by default
`kompile` optimizes the generated model for execution.  In particular, it
does not insert any backtracking markers where transition attempts should be
made, so `krun` lacks the information it needs to exhaustively search the
generated language model.  Like with the other options, we also have to
explicitly tell `kompile` which rules should be considered as actual
transitions.  A theoretically correct but practically unfeasible approach
to search all possible behaviors is to consider all rules as transitions.
Even more than in the case of `superheating` and `supercooling`, such a naive
solution would make the number of behaviors, and thus `krun`, explode.
Remember that a two-thread program with 150 statements each manifests more
behaviors than particles in the known universe!  Consequently, unless your
multi-threaded programs are very small, you will most likely want to control
which rules should be considered transitions and which should not.

A good rule of thumb is to include as transitions only those rules which
*compete for behaviors*.  That is, those rules which may yield a different
behavior if we choose to apply them when other rules match as well.
The rule for addition, for example, is a clear example of a rule which
should not be a transition: indeed, `3+7` will rewrite to `10` now and also
later.  On the other hand, the lookup rule should be a transition.  Indeed,
if we delay the lookup of variable `x`, then other threads may write `x` in the
meanwhile (with an increment or an assignment rule) and thus yield a
different behavior.

Let us tag those rules which should be transitions: lookup and increment need
to be transitions (they may be already tagged, because they happened to also
be `supercool` rules); the read rule needs to also be a transition, because it
may complete with other instances of itself in other threads; assignment
needs to also be a transition, and so should be the first rule for print.

Let us now `kompile` with the transition option set as desired:

    kompile imp --transition="lookup increment assignment read print"

Now `echo 23 | krun spawn.imp --search` gives us all 10 behaviors of the
spawn program.
  
It is highly non-trivial to say precisely which rules need to be transitions,
so `krun` makes no attempt to automatically detect it.  Instead, it provides the
functionality to let you decide it.

We currently have no mechanism for thread synchronization.  In the next lesson
we add a join statement, which allows a thread to wait until another completes.
