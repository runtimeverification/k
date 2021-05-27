# Lesson 1.7: Side Conditions and Rule Priority

The purpose of this lesson is to explain how to write conditional rules in K, 
and to explain how to control the order in which rules are tried.

## Side Conditions

So far, all of the rules we have discussed have been **unconditional rules**.
If the left hand side of the rule matches the arguments to the function, the
rule applies. However, there is another type of rule, a **conditional rule**.
A conditional rule consists of a **rule body** containing the patterns to
match, and a **side condition** representing a Boolean expression that must
evaluate to true in order for the rule to apply.

Side conditions in K are introduced via the `requires` keyword immediately
following the rule body. For example, here is a rule with a side condition
(`lesson-07-a.k`):

```k
module LESSON-07-A
  imports BOOL
  imports INT

  syntax Bool ::= isPositive(Int) [function]

  rule isPositive(I) => true
    requires I >Int 0
endmodule
```

In this case, the `isPositive` function takes a single integer argument. The
function evaluates to true if the argument passed is greater than zero. Note
that the side condition is allowed to refer to variables that appear on the
left-hand-side of the rule. In the same manner as variables appearing on the
right-hand-side, variables that appear in the side condition evaluate to the
value that was matched on the left hand side. Then the functions in the
side condition are evaluated, which returns a term of sort `Bool`. If the term
is equal to `true`, then the rule applies. Bear in mind that the side condition
is only evaluated at all if the patterns on the left-hand-side of the rule
match the term being evaluated.

### Exercise

Write a rule that evaluates `isPositive` to `false` if the argument to the
function is zero or negative. Test that the function correctly evaluates 
various positive, zero, and negative integers.

## `owise` Rules

So far, all the rules we have introduced have had the same **priority**. What
this means is that K does not necessarily enforce an order in which the rules
are tried. We have only discussed functions so far in K, so it is not
immediately clear why this choice was made, given that a function is not
considered well-defined if multiple rules for evaluating it are capable of
evaluating the same arguments to different results. However, in future lessons
we will discuss other types of rules in K, some of which can be
**nondeterministic**. What this means is that if more than one rule is capable
of matching, then K will explore both possible rules in parallel, and consider
each of their respective results when executing your program. Don't worry too
much about this right now, but just understand that because of the potential
later for nondeterminism, we don't enforce a total ordering on the order in
which rules are attempted to be applied.

However, sometimes this is not practical; It can be very convenient to express
that a particular rule applies if no other rules for that function are
applicable. This can be expressed by adding the `owise` attribute to a rule.
What this means, in practice, is that this rule has lower priority than other
rules, and will only be tried to be applied after all the other,
higher-priority rules have been tried and they have failed.

For example, in the above exercise, we had to add a side condition to the rule
we wrote to handle `isPositive` for negative numbers. However, in practice this
meant that the integer comparison operation happened twice. We can more
efficiently and more idiomatically write the negative case for the `isPositive`
rule using the `owise` attribute (`lesson-07-b.k`):

```k
module LESSON-07-B
  imports BOOL
  imports INT

  syntax Bool ::= isPositive(Int) [function]

  rule isPositive(I) => true  requires I >Int 0
  rule isPositive(_) => false [owise] 
endmodule
```

Note that we have introduced a new piece of syntax here: `_`. This is actually
just a variable. However, as a special case, when a variable is named `_`, it
does not bind a value that can be used on the right hand side of the rule, or
in a side condition. Effectively, `_` is a placeholder variable that means "I
don't care about this term."

This rule is saying, "if the first rule does not apply, then the result of the
function is false." Note, however, that `owise` can be used in more complicated
ways. For example, you can perform additional matching in an `owise` rule. You
can also have multiple higher-priority rules, or multiple `owise` rules. What
this means in practice is that all of the non-`owise` rules are tried first, in
any order, followed by all the `owise` rules, in any order.

### Exercise

Reverse the rules defining `isPositive` so that the case for zero and negative
numbers is tried first, and the positive case is handled via an `owise` rule.
Test that the output of the function is the same either way.

## Rule Priority

As it happens, the `owise` attribute is a specific case of a more general
concept we call **rule priority**. In essence, each rule is assigned an integer
priority. Rules are tried in increasing order of priority, starting with a
rule with priority zero, and trying each increasing numerical value
successively.

By default, a rule is assigned a priority of 50. If the rule has the `owise`
attribute, it is instead given the priority 200. You can see why this will
cause `owise` rules to be tried after regular rules.

However, it is also possible to directly assign a numerical priority to a rule
via the `priority` attribute. For example, here is an alternative way
we could express the `isPositive` function (`lesson-07-c.k`):

```k
module LESSON-07-C
  imports BOOL
  imports INT

  syntax Bool ::= isPositive(Int) [function]

  rule isPositive(I) => true
    requires I >Int 0 [priority(50)]
  rule isPositive(_) => false [priority(200)] 
endmodule
```

We can, of course, assign a priority equal to any non-negative integer. For
example, here is a more complex example (`lesson-07-d.k`):

```k
module LESSON-07-D
  imports INT
  imports BOOL

  syntax Int ::= foo(Int) [function]

  rule foo(I) => 0 requires I <=Int 1 [priority(50)]
  rule foo(I) => 1 requires I <=Int 10 [priority(51)]
  rule foo(I) => 2 requires I <=Int 100 [priority(52)]
  rule foo(_) => 3 [priority(53)]
endmodule
```

Here we have explicitly expressed the order in which the rules of this
function are tried. Since rules are tried in increasing numerical priority,
we first try the rule with priority 50, then 51, then 53, and finally 53.

As a final note, remember that if you assign a rule a priority higher than 200,
it will be tried **after** a rule with the `owise` attribute, and if you assign
a rule a priority less than 50, it will be tried **before** a rule with no
explicit priority.

## Exercises

1. Write a function `isEven` that returns whether an integer is an even number.
Use only two rules and one side condition. Refer back to
[domains.md](../../../include/kframework/builtin/domains.md) for the relevant
integer operations.

2. Modify the calculator application from lesson 6, problem 2, so that division
by zero will no longer make `krun` crash with a "Divison by zero" exception.
Instead, the `/` function should not match any of its rules if the denominator
is zero.
