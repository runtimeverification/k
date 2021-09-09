# Lesson 1.21: Unification and Symbolic Execution

The purpose of this lesson is to teach the basic concepts of symbolic execution
in order to introduce the unique capabilities of the Haskell Backend at a
conceptual level.

## Symbolic Execution

Thus far, all of the programs we have run using K have been **concrete**
configurations. What this means is that the configuration we use to initialize
the K rewrite engine is concrete; in other words, contains no logical
variables. The LLVM Backend is a **concrete execution** engine, meaning that
it is only capable of rewriting concrete configurations.

By contrast, the Haskell Backend performs **symbolic execution**, which is
capable of rewriting any configuration, including those where parts of the
configuration are **symbolic**, ie, contain variables or uninterpreted
functions.

## Unification

Previusly, we have introduced the concept that K rewrite rules operate by means
of pattern matching: the current configuration being rewritten is pattern
matched against the left-hand side of the rewrite rule, and the substitution
is used in order to construct a new term from the right-hand side. In symbolic
execution, we use
[unification](https://en.wikipedia.org/wiki/Unification_%28computer_science%29)
instead of pattern matching. To summarize, unification behaves akin to a
two-way pattern matching where both the configuration and the left-hand side
of the rule can contain variables, and the algorithm generates a
**most general unifier** containing substitutions for the variables in both
which will make both terms equal.

## Feasibility

Unification by itself cannot completely solve the problem of symbolic
execution. One task symbolic execution must perform is to identify whether
a particular symbolic term is **feasible**, that is to say, that there actually
exists a concrete instantiation of that term such that all the logical
constraints on that term can actually be satisfied. The Haskell Backend
delegates this task to [Z3](https://github.com/Z3Prover/z3), a 
[SMT solver](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories).
This solver is used to periodically trim configurations that are determined
to be mathematically infeasible.

## Symbolic terms

The final component of symbolic execution consists of the task of introducing
symbolic terms into the configuration. This can be done one of two different
ways. First, the term being passed to `krun` can actually be symbolic. This
is less frequently used because it requires the user to construct an AST
that contains variables, something which our current parsing capabilities are
not well-equipped to do. The second, more common, way of introducing symbolic
terms into a configuration consists of writing rules where there exists an
existentially qualified variable on the right-hand side of the rule that does
not exist on the left-hand side of the rule.

In order to prevent users from writing such rules by accident, K requires
that such variables begin with the `?` prefix. For example, here is a rule
that rewrites a constructor `foo` to a symbolic integer:

```
rule foo => ?X:Int
```

When this rule applies, a variable is introduced to the configuration, which
then is unified against the rules that might apply in order to symbolically
execute that configuration.

### `ensures` clauses

We also introduce here a new feature of K rules that applies when a rule
has this type of variable on the right-hand side: the `ensures` clause.
An `ensures` clause is similar to a `requires` clause and can appear after
a rule body, or after a `requires` clause. The `ensures` clause is used to
introduce constraints that might apply to the variable that was introduced by
that rule. For example, we could write the rule above with the additional
constraint that the symbolic integer that was introduced must be less than
five, by means of the following rule:

```
rule foo => ?X:Int ensures ?X <Int 5
```

## Putting it all together

Putting all these pieces together, it is possible to use the Haskell Backend
to perform symbolic reasoning about a particular K module, determining all the
possible states that can be reached by a symbolic configuration.

For example, consider the following K definition (`lesson-21.k`):

```k
module LESSON-21
    imports INT

    rule <k> 0 => ?X:Int ... </k> ensures ?X =/=Int 0
    rule <k> X:Int => 5  ... </k> requires X >=Int 10
endmodule
```

When we symbolically execute the program `0`, we get the following output
from the Haskell Backend:

```
    <k>
      5 ~> .
    </k>
  #And
    {
      true
    #Equals
      ?X:Int >=Int 10
    }
  #And
    #Not ( {
      ?X:Int
    #Equals
      0
    } )
#Or
    <k>
      ?X:Int ~> .
    </k>
  #And
    #Not ( {
      true
    #Equals
      ?X:Int >=Int 10
    } )
  #And
    #Not ( {
      ?X:Int
    #Equals
      0
    } )
```

Note some new symbols introduced by this configuration: `#And`, `#Or`, and
`#Equals`. While `andBool`, `orBool`, and `==K` represent functions of sort
`Bool`, `#And`, `#Or`, and `#Equals` are **matching logic connectives**. We
will discuss matching logic in more detail later in the tutorial, but the basic
idea is that these symbols represent Boolean operators over the domain of
configurations and constraints, as opposed to over the `Bool` sort.

Notice that the configuration listed above is a disjunction of conjunctions.
This is the most common form of output that can be produced by the Haskell
Backend. In this case, each conjunction consists of a configuration and a pair
of constraints. What this conjunction describes, essentially, is a
configuration and a set of information that was derived to be true while
rewriting that configuration.

Similar to how we saw `--search` in a previous lesson, the reason we have
multiple disjuncts is because there are multiple possible output states
for this program, depending on whether or not the second rule applied. In the
first case, we see that `?X` is greater than or equal to 10, so the second rule
applied, rewriting the symbolic integer to the concrete integer 5. In the
second case, we see that the second rule did not apply because `?X` is less
than 10. Moreover, because of the `ensures` clause on the first rule, we know
that `?X` is not zero, therefore the second rule will not apply a second time.
If we had omitted this constraint, we would have ended up infinitely applying
the first rule, leading to `krun` not terminating.

In the next lesson, we will cover how symbolic execution forms the backbone
of deductive program verification in K and how we can use K to prove programs
correct against a specification.

## Exercises

1. Create another rule in `LESSON-21` that rewrites odd integers greater than
ten to a symbolic even integer less than 10 and greater than 0. This rule will
now apply nondeterministically along with the existing rules. Predict what the
resulting output configuration will be from rewriting `0` after adding this
rule. Then run the program and see whether your prediction is correct.
