<!-- Copyright (c) 2012-2014 K Team. All Rights Reserved. -->
### Parallel Type Checkers/Inferencers

[MOVIE []]()

In this lesson you learn how to define parallel type checkers or
inferencers.  For the sake of a choice, we will parallelize the one in
the previous lesson, but the ideas are general.  We are using the same
idea to define type checkers for other languages in the K tool
distribution, such as SIMPLE and KOOL.

The idea is in fact quite simple.  Instead of one monolithic typing
task, we generate many smaller tasks, which can be processed in
parallel.  We use the same approach to define parallel semantics as we
used for threads in IMP++ in Part 4 of the tutorial, that is, we add a
cell holding all the parallel tasks, making sure we declare the cell
holding a task with multiplicity `*`.  For the particular type
inferencer that we chose here, the one in Lesson 5, each task will
hold an expression to type together with a type environment (so it
knows where to lookup its free variables).  We have the following
configuration then:

    configuration <tasks color="yellow">
                    <task color="orange" multiplicity="*">
                      <k color="green"> $PGM:Exp </k>
                      <tenv color="red"> .Map </tenv>
                    </task>
                  </tasks>
                  <mgu color="blue"> .Mgu </mgu>

Now we have to take each typing rule we had before and change it to
yield parallel typing.  For example, our rule for typing
multiplication was the following in Lesson 5:

    rule T1:Type * T2:Type => T1 = int ~> T2 = int ~> int

Since `*` was strict, its two arguments eventually type, and once that
happens the rule above fires.  Unfortunately, the strictness of
multiplication makes the typing of the two expressions sequential in
our previous definition.  To avoid typing the two expressions
sequentially and instead generating two parallel tasks, we remove the
`strict` attribute of multiplication and replace the rule above with the
following:

    rule <k> E1 * E2 => int ...</k> <tenv> Rho </tenv>
         (. => <task> <k> E1 = int </k> <tenv> Rho </tenv> </task>
               <task> <k> E2 = int </k> <tenv> Rho </tenv> </task>)

Therefore, we generate two tasks for typing `E1` and `E2` in the same type
environment as the current task, and let the current task continue by
simply optimistically reducing `E1*E2` to its expected result type, `int`.
If `E1` or `E2` will not type to `int`, then either their corresponding
tasks will get stuck or the `<mgu/>` cell will result into a clash or cycle,
so the program will not type overall in spite of the fact that we
allowed the task containing the multiplication to continue.  This is
how we get maximum of parallelism in this case.

Before we continue, note that the new tasks hold equalities in them,
where one of its arguments is an expression, while previously the
equality construct was declared to take types.  What we want now is
for the equality construct to possibly take any expressions, and first
type them and then generate the type constraint like before.  This can
be done very easily by just extending the equality construct to
expressions and declaring it `strict`:

    syntax KItem ::= Exp "=" Exp  [strict]

Unlike before, where we only passed types to the equality construct,
we now need a runtime check that its arguments are indeed types before
we can generate the `updateMgu` command:

    rule <k> T:Type = T':Type => . ...</k>
         <mgu> Theta:Mgu => updateMgu(Theta,T,T') </mgu>

Like before, an equality will therefore update the `<mgu/>` dell and then
it dissolves itself, letting the `<k/>` cell in the corresponding task
empty.  Such empty tasks are unnecessary, so they can be erased:

    rule <task>... <k> . </k> ...</task> => .

We can now follow the same style as for multiplication to write the
parallel typing rules of the other arithmetic constructs, and even for
the conditional.

To parallelize the typing of lambda we generate two fresh types, one
for the variable and one for the body, and make sure that we generate
the correct type constraint and environment in the body task:

    rule <k> lambda X . E => Tx -> Te ...</k> <tenv> TEnv </tenv>
         (. => <task> <k> E = Te </k> <tenv> TEnv[Tx/X] </tenv> </task>)
      when fresh(Tx:Type) andBool fresh(Te:Type)

Note that the above also allows us to not need to change and then
recover the environment of the current cell.

For function application we also need to generate two fresh types:

    rule <k> E1 E2 => T ...</k> <tenv> Rho </tenv>
         (. => <task> <k> E1 = T2 -> T </k> <tenv> Rho </tenv> </task>
               <task> <k> E2 = T2 </k> <tenv> Rho </tenv> </task>)
      when fresh(T2:Type) andBool fresh(T:Type)

The only rule left is that of `mu X . E`.  In this case we only need one
fresh type, because `X`, `E` and `mu X . E` have all the same type:

    rule <k> mu X . E => T ...</k>  <tenv> TEnv </tenv>
         (. => <task> <k> E = T </k> <tenv> TEnv[T/X] </tenv> </task>)
      when fresh(T:Type)

We do not need the type environment recovery operation, so we delete it.

We can now `kompile` and `krun` all the programs that we typed in Lesson 5.
Everything should work.

In this lesson we only aimed at parallelizing the type inferencer in
Lesson 5, not to improve its expressivity; it still has the same
limitations in terms of polymorphism.  The next lessons are dedicated
to polymorphic type inferencers.
