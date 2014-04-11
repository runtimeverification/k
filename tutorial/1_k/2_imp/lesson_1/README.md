<!-- Copyright (C) 2010-2014 K Team. All Rights Reserved. -->

### Defining a More Complex Syntax

Here we learn how to define a more complex language syntax than LAMBDA's,
namely the C-like syntax of IMP.  Also, we will learn how to define languages
using multiple modules, because we are going to separate IMP's syntax from
its semantics using modules.  Finally, we will also learn how to use K's
builtin support for syntactic lists.

The K tool provides modules for grouping language features.  In general, we
can organize our languages in arbitrarily complex module structures.
While there are no rigid requirements or even guidelines for how to group
language features in modules, we often separate the language syntax from the
language semantics in different modules.

In our case here, we start by defining two modules, IMP-SYNTAX and IMP, and
import the first in the second, using the keyword `imports`.  As their names
suggest, we will place all IMP's syntax definition in IMP-SYNTAX and all its
semantics in IMP.

Note, however, that K does no more than simply includes all the
contents of the imported module in the one which imports it (making sure
that everything is only kept once, even if you import it multiple times).
In other words, there is currently nothing fancy in K tool's module system.

IMP has six syntactic categories, as shown in `imp.k`: `AExp` for arithmetic
expressions, `BExp` for Boolean expressions, `Block` for blocks, `Stmt` for
statements, `Pgm` for programs and Ids for comma-separated lists of
identifiers.  Blocks are special statements, whose role is to syntactically
constrain the conditional statement and the while loop statement to only
take blocks as branches and body, respectively.

There is nothing special about arithmetic and Boolean expressions.  
They are given the expected strictness attributes, except for `<=` and `&&`,
for demonstration purposes.

The `<=` is defined to be `seqstrict`, which means that it evaluates its
arguments in order, from left-to-right (recall that the `strict` operators
can evaluate their arguments in any, fully interleaved, orders).  Like
`strict`, the `seqstrict` annotation can also be configured; for example, one
can specify in which arguments and in what order.  By default, `seqstrict`
refers to all the arguments, in their left-to-right order.  In our case here,
it is equivalent with `seqstrict(1 2)`.

The `&&` is only strict in its first argument, because we will give it a
short-circuited semantics (its second argument will only be evaluated when
the first evaluates to true).  Recall the K tool also allows us to associate
Latex attributes to constructs, telling the document generator how to display
them.  For example, we associate `<=` the attribute `latex({#1}\leq{#2})`,
which makes it be displayed $\leq$ everywhere in the generated documentation.

In this tutorial we take the freedom to associate the various constructs
parsing precedences that we have already tested and we know work well, so that
we can focus on the semantics here instead of syntax.  In practice, though,
you typically need to experiment with precedences until you obtain the desired
parser.

Blocks are defined using curly brackets, and they can either be empty or
hold a statement.

Nothing special about the IMP statements.  Note that `;` is an assignment
statement terminator, not a statement separator.  Note also that blocks are
special statements.

An IMP program declares a comma-separated list of variables using the keyword
`int` like in C, followed by a semicolon `;`, followed by a statement.
Syntactically, the idea here is that we can wrap any IMP program within a
`main(){...}` function and get a valid C program.  IMP does not allow variable
declarations anywhere else except through this construct, at the top-level of
the program.  Other languages provided with the \K distribution (see, e.g., the
IMP++ language also discussed in this tutorial) remove this top-level program
construct of IMP and add instead variable declaration as a statement construct,
which can be used anywhere in the program, not only at the top level.

Note how we defined the comma-separated list of identifiers, using
`List{Id,","}`.  The K tool provides builtin support for generic syntactic
lists.  In general,

    syntax B ::= List{A,T}

declares a new non-terminal, `B`, corresponding to `T`-separated sequences of
elements of `A`, where `A` is a non-terminal and `T` is a terminal.  These
lists can also be empty, that is, IMP programs declaring no variable are also
allowed (e.g., `int; {}` is a valid IMP program).  To instantiate and use
the K builtin lists, you should alias each instance with a (typically fresh)
non-terminal in your syntax, like we do with the `Ids` nonterminal.

Like with other K features, there are ways to configure the syntactic lists,
but we do not discuss them here.

Recall from Tutorial 1 (LAMBDA) that in order for strictness to work well
we also need to tell K which computations are meant to be results.  We do
this as well now, in the module IMP: integers and Booleans are K results.

Kompile `imp.k` and test the generated parser by running some programs.
Since IMP is a fragment of C, you may want to select the C mode in your
editor when writing these programs.  This will also give your the feel that
you are writing programs in a real programming language.

For example, here is `sum.imp`, which sums in sum all numbers up to n:

    int n, sum;
    n = 100;
    sum=0;
    while (!(n <= 0)) {
      sum = sum + n;
      n = n + -1;
    }

Now krun it and see how it looks parsed in the default `k` cell.

The program `collatz.imp` tests the Collatz conjecture for all numbers up to
m and accumulates the total number of steps in s:

    int m, n, q, r, s;
    m = 10;
    while (!(m<=2)) {
      n = m;
      m = m + -1;
      while (!(n<=1)) {
        s = s+1;
        q = n/2;
        r = q+q+1;
        if (r<=n) {
          n = n+n+n+1;         // n becomes 3*n+1 if odd
        } else {n=q;}          //        of   n/2 if even
      }
    }

Finally, program `primes.imp` counts in `s` all the prime numbers up to `m`:

    int i, m, n, q, r, s, t, x, y, z;
    m = 10;  n = 2;
    while (n <= m) {
      // checking primality of n and writing t to 1 or 0
      i = 2;  q = n/i;  t = 1;
      while (i<=q && 1<=t) {
        x = i;
        y = q;
        // fast multiplication (base 2) algorithm
        z = 0;
        while (!(x <= 0)) {
          q = x/2;
          r = q+q+1;
          if (r <= x) { z = z+y; } else {}
          x = q;
          y = y+y;
        } // end fast multiplication
        if (n <= z) { t = 0; } else { i = i+1;  q = n/i; }
      } // end checking primality
      if (1 <= t) { s = s+1; } else {}
      n = n+1;
    }

All the programs above will run once we define the semantics of IMP.  If you
want to execute them now, wrap them in a `main(){...}` function and compile
them and run them with your favorite C compiler.

Before we move to the K semantics of IMP, we would like to make some
clarifications regarding the K builtin parser, `kast`.  Although it is quite
powerful, you should not expect magic from it!  While the K parser can parse
many non-trivial languages (see, for example, the KOOL language in
[tutorial/2_languages](/tutorial/2_languages)) in the K distribution), it was
never meant to be a substitute for real parsers.  We often call the syntax
defined in K *the syntax of the semantics*, to highlight the fact that its
role is to serve as a convenient notation when writing the semantics, not
necessarily as a means to define concrete syntax of arbitrarily complex
programming languages.  See the KERNELC language in [samples](/samples/)
for an example on how to connect an external parser for concrete syntax to
the K tool.

The above being said, we strongly encourage you to strive to make the
builtin parser work with your desired language syntax!  Do not give up
simply because you don't want to deal with syntactic problems.  On the
contrary, fight for your syntax!  If you really cannot define your desired
syntax because of tool limitations, we would like to know.  Please tell us.

Until now we have only seen default configurations.  In the next lesson we
will learn how to define a K custom configuration.
