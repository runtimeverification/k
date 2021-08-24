# Lesson 1.18: Term Equality and the Ternary Operator

The purpose of this lesson is to introduce how to compare equality of terms in
K, and how to put conditional expressions directly into the right-hand side of
rules.

## Term Equality

One major way you can compare whether two terms are equal in K is to simply
match both terms with a variable with the same name. This will only succeed
in matching if the two terms are equal structurally. However, sometimes this
is impractical, and it is useful to have access to a way to actually compare
whether two terms in K are equal. The operator for this is found in
[domains.md](../../../include/kframework/builtin/domains.md) in the `K-EQUAL`
module. The operator is `==K` and takes two terms of sort `K` and returns a
`Bool`. It returns true if they are equal. This includes equality over builtin
types such as `Map` and `Set` where equality is not purely structural in
nature. However, it does not include any notion of semantic equality over
user-defined syntax. The inverse symbol for inequality is `=/=K`.

## Ternary Operator

One way to introduce conditional logic in K is to have two separate rules,
each with a side condition (or one rule with a side condition and another with
the `owise` attribute). However, sometimes it is useful to explicitly write
a conditional expression directly in the right-hand side of a rule. For this
purpose, K defines one more operator in the `K-EQUAL` module, which corresponds
to the usual ternary operator in many languages. Here is an example of its 
usage (`lesson-18.k`):

```k
module LESSON-18
  imports INT
  imports BOOL
  imports K-EQUAL

  syntax Exp ::= Int | Bool | "if" "(" Exp ")" Exp "else" Exp [strict(1)]

  syntax Bool ::= isKResult(K) [function, symbol]
  rule isKResult(_:Int) => true
  rule isKResult(_:Bool) => true

  rule if (B:Bool) E1:Exp else E2:Exp => #if B #then E1 #else E2 #fi
endmodule
```

Note the symbol on the right-hand side of the final rule. This symbol is
polymorphic: `B` must be of sort `Bool`, but `E1` and `E2` could have been
any sort so long as both were of the same sort, and the sort of the entire
expression becomes equal to that sort. K supports polymorphic built-in
operators, but does not yet allow users to write their own polymorphic
productions.

The behavior of this function is to evaluate the Boolean expression to a
Boolean, then pick one of the two children and return it based on whether the
Boolean is true or false. Please note that it is not a good idea to use this
symbol in cases where one or both of the children is potentially undefined
(for example, an integer expression that divides by zero). While the default
implementation is smart enough to only evaluate the branch that happens to be
picked, this will not be true when we begin to do program verification. If
you need short circuiting behavior, it is better to use a side condition.

## Exercises

1. Write a function in K that takes two terms of sort `K` and returns an
`Int`: the `Int` should be 0 if the terms are equal and 1 if the terms are 
unequal.

2. Modify your solution to Lesson 1.16, Problem 1 and introduce an `if`
`Stmt` to the syntax of the language, then implement it using the `#if` symbol.
Make sure to write tests for the resulting interpreter.

## Next lesson

Once you have completed the above exercises, you can continue to
[Lesson 1.19: Debugging with GDB](../19_debugging/README.md).
