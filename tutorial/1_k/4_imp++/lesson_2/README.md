<!-- Copyright (C) 2010-2014 K Team. All Rights Reserved. -->

### Configuration Refinement; Freshness

To prepare for the semantics of threads and local variables, in this lesson we
split the state cell into an environment and a store.  The environment and
the store will be similar to those in the definition of LAMBDA++ in Part
3 of the Tutorial.  This configuration refinement will require us to change
some of IMP's rules, namely those that used the state.

To split the state map, which binds program variables to values, into an
environment mapping program variables to locations and a store mapping
locations to values, we replace in the configuration declaration the cell

    <state color="red"> .Map </state>

with two cells

    <env color="LightSkyBlue"> .Map </env>
    <store color="red"> .Map </store>

`Structurally` speaking, this split of a cell into other cells is a major
semantic change, which, unfortunately, requires us to revisit the existing
rules that used the state cell.  Once could, of course, argue that we could
have avoided this problem if we had followed from the very beginning the
good-practice style to work with an environment and a store, instead of a
monolithic state.  While that is a valid argument, highlighting the fact that
modularity is not only a feature of the framework alone, but one should also
follow good practices to achieve it, it is also true that if all we wanted
in Part 2 of the tutorial was to define IMP as is, then the split of the state
in an environment and a store is unnecessary and not really justified.

The first rule which used a state cell is the lookup rule:

    rule <k> X:Id => I ...</k> <state>... X |-> I ...</state>

We modify it as follows:

    rule <k> X:Id => I ...</k>
         <env>... X |-> N ...</env>
         <store>... N |-> I ...</store>

So we first match the location `N` of `X` in the environment, then the value
`I` at location `N` in the store, and finally we rewrite `X` to `I` into the
computation.  This rule also shows an instance of a more complex
multiset matching, where two variables (`X` and `N`) are matched each twice.

The assignment rule is modified quite similarly.

The variable declaration rule is trickier, though, because we need to allocate
a fresh location in the store and bind the newly declared variable to it.
This is quite similar to the way we allocated space for variables in
the environment-based definition of LAMBDA++ in Part 3 of the tutorial.

    rule <k> int (X,Xs => Xs); ...</k>
         <env> Rho:Map => Rho[N/X] </env>
         <store>... .Map => N|->0 ...</store>
      when fresh(N:Nat)

The side condition `fresh(N:Nat)` generates an *element* of sort `Nat` that has
not been generated so far.  We emphasized *element*, because, like also
explained in the LAMBDA++ tutorial, technically it is nothing but K syntactic
sugar for a straightforward operation: it generates a term of the form
`symNat(n)` of sort `Nat`, or something similar (because the internal
representation of symbolic numbers may change in the K implementation), where
`n` is a natural number, thought of as the `n`-th symbolic natural number that
had been generated so far; the counter `n` is maintained in a cell that the K
tool automatically adds to the configuration for this purpose.

`kompile` and `krun` `sum.imp` to see how the fresh locations have been
generated and used.  There were two fresh locations needed, for the two
variables.  Note also that a cell holding the counter has been added to the
configuration.

In the next lesson we will add the semantics of variable increment, and see
how that yields non-deterministic behaviors in programs and how to explore
those behaviors using the K tool.
