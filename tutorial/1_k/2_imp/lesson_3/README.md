<!-- Copyright (C) 2010-2014 K Team. All Rights Reserved. -->

### Computations, Results, Strictness; Rules Involving Cells

In this lesson we will learn about the syntactic category K of computations,
about how strictness attributes are in fact syntactic sugar for rewrite rules
over computations, and why it is important to tell the tool which
computations are results.  We will also see a K rule that involves cells.

##### K Computations

Computation structures, or more simply *computations*, extend the abstract
syntax of your language with a list structure using `~>` (read  *followed
by* or *and then*, and written $\curvearrowright$ in Latex) as a separator.
K provides a distinguished sort, K, for computations.  The extension of the
abstract syntax of your language into computations is done automatically by
the K tool when you declare constructs using the `syntax` keyword, so the K
semantic rules can uniformly operate only on terms of sort K.  The intuition
for computation structures of the form

    t1 ~> t2 ~> ... ~> tn

is that the listed tasks are to be processed in order.  The initial
computation typically contains the original program as its sole task, but
rules can then modify it into task sequences, as seen shortly.

##### Strictness in Theory

The strictness attributes, used as annotations to language constructs,
actually correspond to rules over computations.  For example, the
`strict(2)` attribute of the assignment statement corresponds to the
following two opposite rules (`X` ranges over `Id` and `A` over `AExp`):

    X=A; => A ~> X=[];
    A ~> X=[]; => X=A;

The first rule pulls `A` from the syntactic context X=A; and schedules it
for processing.  The second rule plugs `A` back into its context.
Inspired from the chemical abstract machine, we call rules of the first
type above *heating* rules and rules of the second type *cooling* rules.
Similar rules are generated for other arguments in which operations are
strict.  Iterative applications of heating rules eventually bring to the
top of the computation atomic tasks, such as a variable lookup, or a
builtin operation, which then make computational progress by means of other
rules.  Once progress is made, cooling rules can iteratively plug the result
back into context, so that heating rules can pick another candidate for
reduction, and so and so forth.

When operations are strict only in some of their arguments, the corresponding
positions of the arguments in which they are strict are explicitly enumerated
in the argument of the `strict` attribute, e.g., `strict(2)` like above, or
`strict(2 3)` for an operation strict in its second and third arguments, etc.
If an operation is simply declared `strict` then it means that it is strict
in all its arguments.  For example, the strictness of addition yields:

    A1+A2 => A1 ~> []+A2
    A1 ~> []+A2 => A1+A2
    A1+A2 => A2 ~> A1+[]
    A2 ~> A1+[] => A1+A2

It can be seen that such heating/cooling rules can easily lead to
non-determinism, since the same term may be heated many different ways;
these different evaluation orders may lead to different behaviors in some
languages (not in IMP, because its expressions do not have side effects,
but we will experiment with non-determinism in its successor, IMP++).

A similar desugaring applies to sequential strictness, declared with the
keyword `seqstrict`.  While the order of arguments of `strict` is irrelevant,
it matters in the case of `seqstrict`: they are to be evaluated in the
specified order; if no arguments are given, then they are assumed by default
to be evaluated from left-to-right.  For example, the default heating/cooling
rules associated to the sequentially strict `<=` construct above are
(`A1`, `A2` range over `AExp` and `I1` over `Int`):

    A1<=A2 => A1 ~> []<=A2
    A1 ~> []<=A2 => A1<=A2
    I1<=A2 => A2 ~> I1<=[]
    A2 ~> I1<=[] => I1<=A2

In other words, `A2` is only heated/cooled after `A1` is already evaluated.

While the heating/cooling rules give us a nice and uniform means to define
all the various allowable ways in which a program can evaluate, all based
on rewriting, the fact that they are reversible comes with a serious practical
problem: they make the K definitions unexecutable, because they lead to
non-termination.

##### Strictness in Practice; K Results

To break the reversibility of the theoretical heating/cooling rules, and,
moreover, to efficiently execute K definitions, the current implementation of
the K tool relies on users giving explicit definitions of their languages'
results.

The K tool provides a predicate `isKResult`, which is automatically defined
as we add syntactic constructs to KResult (in fact the K tool defines such
predicates for all syntactic categories, which are used, for example, as
rule side conditions to check user-declared variable memberships, such as
`V:Val` stating that `V` belongs to `Val`).

The kompile tool, depending upon what it is requested to do, changes the
reversible heating/cooling rules corresponding to evaluation strategy
definitions (e.g., those corresponding to strictness attributes) to avoid
non-termination.  For example, when one is interested in obtaining an
executable model of the language (which is the default compilation mode of
kompile), then heating is performed only when the to-be-pulled syntactic
fragment is not a result, and the corresponding cooling only when the
to-be-plugged fragment is a result.  In this case, e.g., the heating/cooling
rules for assignment are modified as follows:

    X=A; => A ~> X=[];   when notBool isKResult(A)
    A ~> X=[]; => X=A;   when isKResult(A)

Note that non-termination of heating/cooling is avoided now.  The only thing
lost is the number of possible behaviors that a program can manifest, but 
this is irrelevant when all we want is one behavior.

As will be discussed in the IMP++ tutorial, the heating/cooling rules are
modified differently by kompile when we are interested in other aspects of the
language definition, such us, for example, in a search-able model that
comprises all program behaviors.  This latter model is obviously more general
from a theoretical perspective, but, in practice, it is also slower to execute.
The kompile tool strives to give you the best model of the language for the
task you are interested in.

##### Can't Results be Inferred Automatically?

This is a long story, but the short answer is: *No!*.  Maybe in some cases
it is possible, but we prefer to not attempt it in the K tool.  For example,
you may not want a stuck computation to count as a result, just because you
forgot a semantic rule!  Besides, in our experience with defining large
languages, it is quite useful to take your time and think of what the results
of your language's computations are.  This fact in itself may help you
improve your overall language design.  We typically do it at the same time
with defining the evaluation strategies of our languages.

So sorry: you currently do have to explicitly define your K results if you
want to effectively use the K tool.  Note, however, that theoretical
definitions, not meant to be executed, need not worry about defining results
(that's because in theory semantic rules apply *modulo* the reversible
heating/cooling rules, so results are not necessary).

##### A K Rule Involving Cells

All our K rules so far in the tutorial were of the form

    rule left => right when condition

where left and right were syntactic, or more generally computation, terms.

Here is our first K rule explicitly involving cells:

    rule <k> X:Id => I ...</k> <state>... X |-> I ...</state>

Recall that the `k` cell holds computations, which are sequences of tasks
separated by `~>`.  Also, the state cell holds a map, which is a set of
bindings, each binding being a pair of computations (currently, the
K builtin data-structures, like maps, are untyped; or, said differently,
they are all over the type of computations, K).

Therefore, the two cells mentioned in the rule above hold collections
of things, ordered or not.  The `...`s, which we also call cell *frames*,
stand for *more stuff there, but stuff that we do not care about*.

The rewrite relation `=>` is allowed in K to appear anywhere in a term, its
meaning being that the corresponding subterm is rewritten as indicated in the
shown context.  We say that K's rewriting is *local*.

The rule above says that if the identifier `X` is the first task in the `k`
cell, and if `X` is bound to `I` somewhere in the state, then `X` rewrites
to `I` locally in the `k` cell.  Therefore, variables need to be already
declared when looked up.

Of course, the K rule above can be translated into an ordinary rewrite rule
of the form

    rule <k> X ~> Rest </k> <state> Before (X |-> I) After </state>
      => <k> I ~> Rest </k> <state> Before (X |-> I) After </state>

Besides being more verbose and thus tedious to write, this ordinary rule
is also more error-prone; for example, we may forget the `Rest` variable
in the right-hand-side, etc.  Moreover, the concurrent semantics of K
allows for its rules to be interpreted as concurrent transactions, where
the context is all read-only, while the sub-terms which actually rewrite are
read/write; thus, K rule instances can apply concurrently if they only overlap
on read-only parts, while they cannot if regarded as ordinary rewrite logic
rules.  Note: our current implementation of the K tool is not concurrent,
so K rules are in fact desugared as normal rewrite rules in the K tool.

Kompile `imp.k` using a documentation option and check out how the K rule
looks in the generated document.  The `...` frames are displayed as cell
tears, metaphorically implying that those parts of the cells that we
do not care about are *torn away*.  The rewrite relation is replaced by a
horizontal line: specifically, the subterm which rewrites, `X`, is
underlined, and its replacement is written underneath the line.

In the next lesson we define the complete K semantics of IMP and
run the programs we parsed in the first lesson.
