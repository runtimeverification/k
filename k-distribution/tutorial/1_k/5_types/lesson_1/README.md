### Imperative, Environment-Based Type Systems

[MOVIE [10'11"]](http://youtu.be/WyUxdo7GhtE)

In this lesson you learn how to define a type system for an imperative
language (the IMP++ language defined in Part 4 of the tutorial), using a style
based on type  environments.

Let us copy the `imp.k` file from Part 4 of the tutorial, Lesson 7, which holds
the semantics of IMP++, and modify it into a type system.  The resulting type
system, when executed, yields a type checker.

We start by defining the new strictness attributes of the IMP++ syntax.
While doing so, remember that programs and fragments of programs now reduce
to their types.  So types will be the new results of our new (type) semantics.
We also clean up the semantics by removing the unnecessary tags, and also
use `strict` instead of `seqstrict` wherever possible, because `strict` gives
implementations more freedom.  Interestingly, note that `spawn` is strict now,
because the code of the child thread should type in the current parent's type
environment.

From a typing perspective, the `&&` construct is strict in both its arguments;
its short-circuit (concrete) semantics is irrelevant for its (static) type
system.  Similarly, both the conditional and the while loop are strict
constructs when regarded through the typing lenses.

Finally, the sequential composition is now sequentially strict!  Indeed,
statements are now going to reduce to their type, `stmt`, and it is critical
for sequential composition to type its argument statements left-to-right; 
for example, imagine that the second argument is a variable declaration (whose
type semantics will modify the type environment).

We continue by defining the new results of computations, that is, the actual
types.  In this simple imperative language, we only have a few constant types:
`int`, `bool`, `string`, `block` and `stmt`.

We next define the new configuration, which is actually quite simple.  Besides
the `<k/>` cell, all we need is a type environment cell, `<tenv/>`, which will
hold a map from identifiers to their types.  A type environment is therefore
like a state in the abstract domain of type values.

Let us next modify the semantic rules, turning them into a type system.  In
short, the idea is to reduce the basic values to their types, and then have a
rule for each language construct reducing it to its result type whenever its
arguments have the expected types.

We write the rules in the order given by the syntax declarations, to make
sure we do not forget any construct.

Integers reduce to their type, `int`.

So do the strings.

Variables are now looked up in the type environment and reduced to their type 
there.  Since we only declare integer variables in IMP++, their type in `tenv` 
will always be `int`.  Nevertheless, we write the rule generically, so that we 
would not have to change it later if we add other type declarations to IMP++.
Note that we reject programs which lookup undeclared variables.  Rejection,
in this case, means *rewriting getting stuck*.

Variable increment types to `int`, provided the variable has type `int`.

Read types to `int`, because we only allow integer input.

Division is only allowed on integers, so it rewrites to `int` provided that its
arguments rewrite to `int`.  Note, however, that in order to write `int / int`,
we have to explicitly add `int` to the syntax of arithmetic expressions.
Otherwise, the K parser rightfully complains, because `/` was declared on
arithmetic expressions, not on types.  One simple and generic way to allow
types to appear anywhere, is to define `Type` as a syntactic subcategory of all
the other syntactic categories.  Let's do it on a by-need basis, though.

Addition is overloaded, so we add two typing rules for it: one for integers
and another for strings.

As discussed, `spawn` types to `stmt` provided that its argument types to
`block`.

The assignment construct was `strict(2)`; its typing policy is that the declared
type of `X` should be identical to the type of the assigned value.  Like for
lookup, we define this rule more generically than needed for IMP++, for any 
type, not only for `int`.

The typing rules for Boolean expression constructs are in the same spirit.
Note that we need only one rule for `&&`.

The typing of blocks is a bit trickier.  First, note that we still need to
recover the environment after the block is typed, because we do not want the
block-local variables to be visible in the outer type environment.  We recover
the type environment only after the block-enclosed statements type; moreover,
we also opportunistically yield a `block` type on the computation when we
discard the type environment recovery item.  To account for the fact that the
block-enclosed statement can itself be a block (e.g., `{{S}}`), we would need an
additional rule.  Since we do not like repetition, we instead group the types
`block` and `stmt` into one syntactic category, `BlockOrStmtType`, and now we
can have only one rule.  We also include `BlockOrStmtType` in `Type`, as a
replacement for the two basic types.

The expression statement types as expected.  Recall that we only allow
arithmetic expressions, which type to `int`, to be used as statements in IMP++.

The conditional was declared `strict` in all its arguments.  Its typing policy
is that its first argument types to `bool` and its two branches to `block`.
If that is the case, then it yields a `stmt` type.

For `while`, its first argument should type to `bool` and its second to `block`.

Variable declarations add new bindings to the type environment.  Recall that
we can only declare variables of integer type in IMP++.

The typing policy of `print` is that it can only print integer or string values,
and in that case it types to `stmt`.  Like for `BlockOrStmtType`, to avoid
having two similar rules, one for `int` and another for `string`, we prefer to
introduce an additional syntactic category, `PrintableType`, which includes both
`int` and `string` types.

`halt` types to `stmt`; so its subsequent code is also typed.

`join` types to `stmt`, provided that its argument types to `int`.

Sequential composition was declared as a whitespace-separated sequentially
strict list.  Its typing policy is that all the statements in the list should
type to `stmt` or `block` in order for the list to type to `stmt`.  Since
lists are maintained internally as cons-lists, this is probably the simplest
way to do it:

    rule .Stmts => stmt
    rule _:BlockOrStmtType Ss => Ss

Note that the first rule, which types the empty sequence of statements to `stmt`,
is needed anyway, to type empty blocks `{}` (together with the block rule).

`kompile` `imp.k` and `krun` all the programs in Part 4 of the tutorial.  They
should all type to `stmt`.

In the next lesson we will define a substitution-based type system for LAMBDA.
