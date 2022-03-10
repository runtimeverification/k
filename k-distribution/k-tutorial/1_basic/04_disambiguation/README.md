# Lesson 1.4: Disambiguating Parses

The purpose of this lesson is to teach how to use K's builtin features for
disambiguation to transform an ambiguous grammar into an unambiguous one that
expresses the intended ASTs.

## Priority blocks

In practice, very few formal languages outside the domain of natural language
processing are ambiguous. The main reason for this is that parsing unambiguous
languages is asymptotically faster than parsing ambiguous languages.
Programming language designers instead usually use the notions of operator
precedence and associativity to make expression grammars unambiguous. These
mechanisms work by instructing the parser to reject certain ASTs in favor of
others in case of ambiguities; often it is possible to remove *all* ambiguities
in a grammar with these techniques.

While it is sometimes possible to explicitly rewrite the grammar to remove
these parses, because K's grammar specification and AST generation are
inextricably linked, this is generally discouraged. Instead, we use the
approach of explicitly expressing the relative precedence of different
operators in different situations in order to resolve the ambiguity.

For example, in C, `&&` binds tighter in precedence than `||`, meaning that
the expression `true && false || false` has only one valid AST:
`(true && false) || false`.

Consider, then, the third iteration on the grammar of this definition
(`lesson-04-a.k`):

```k
module LESSON-04-A

  syntax Boolean ::= "true" | "false"
                   | "(" Boolean ")" [bracket]
                   > "!" Boolean [function]
                   > Boolean "&&" Boolean [function]
                   > Boolean "^" Boolean [function]
                   > Boolean "||" Boolean [function]

endmodule
```

In this example, some of the `|` symbols separating productions in a single
block have been replaced with `>`. This serves to describe the
**priority groups** associated with this block of productions.

In this example, the first priority group consists of the atoms of the
language: `true`, `false`, and the bracket operator. In general, a priority
group starts either at the `::=` or `>` operator and extends until either the
next `>` operator or the end of the production block. Thus, we can see that the
second, third, fourth, and fifth priority groups in this grammar all consist
of a single production.

The meaning of these priority groups becomes apparent when parsing programs:
A symbol with a **lesser priority**, (i.e., one that **binds looser**), cannot
appear as the **direct child** of a symbol with a **greater priority** (i.e.,
one that **binds tighter**. In this case, the `>` operator can be seen as a
**greater-than** operator describing a transitive partial ordering on the 
productions in the production block, expressing their relative priority.

To see this more concretely, let's look again at the program
`true && false || false`. As noted before, previously this program was
ambiguous because the parser could either choose that `&&` was the child of `||`
or vice versa. However, because a symbol with lesser priority (i.e., `||`)
cannot appear as the direct child of a symbol with greater priority
(i.e., `&&`), the parser will **reject** the parse where `||` is under the
`&&` operator. As a result, we are left with the unambiguous parse
`(true && false) || false`. Similarly, `true || false && false` parses
unambiguously as `true || (false && false)`. Conversely, if the user explicitly
wants the other parse, they can express this using brackets by explicitly
writing `true && (false || false)`. This still parses successfully because the
`||` operator is no longer the **direct** child of the `&&` operator, but is 
instead the direct child of the `()` operator, and the `&&` operator is an
**indirect** parent, which is not subject to the priority restriction.

Astute readers, however, will already have noticed what seems to be a
contradiction: we have defined `()` as also having greater priority than `||`.
One would think that this should mean that `||` cannot appear as a direct
child of `()`. This is a problem because priority groups are applied to every
possible parse separately. That is to say, even if the term is unambiguous
prior to this disambiguation rule, we still reject that parse if it violates
the rule of priority.

In fact, however, we do not reject this program as a parse error. Why is that?
Well, the rule for priority is slightly more complex than previously described.
In actual fact, it applies only conditionally. Specifically, it applies in
cases where the child is either the first or last production item in the
parent's production. For example, in the production `Bool "&&" Bool`, the
first `Bool` non-terminal is not preceded by any terminals, and the last `Bool`
non-terminal is not followed by any terminals. As a result of this, we apply
the priority rule to both children of `&&`. However, in the `()` operator, 
the sole non-terminal is both preceded by and followed by terminals. As a
result, the priority rule is not applied when `()` is the parent. Because of
this, the program we mentioned above successfully parses.

### Exercise

Parse the program `true && false || false` using kast, and confirm that the AST
places `||` as the top level symbol. Then modify the definition so that you
will get the alternative parse.

## Associativity

Even having broken the expression grammar into priority blocks, the resulting
grammar is still ambiguous. We can see this if we try to parse the following
program (`assoc.bool`):

```
true && false && false
```

Priority blocks will not help us here: the problem comes between two parses
where both possible parses have a direct parent and child which is within a
single priority block (in this case, `&&` is in the same block as itself).

This is where the notion of associativity comes into play. Associativity
applies the following additional rules to parses:

* a left-associative symbol cannot appear as a direct rightmost child of a
symbol with equal priority;
* a right-associative symbol cannot appear as a direct leftmost child of a
symbol with equal priority; and
* a non-associative symbol cannot appear as a direct leftmost **or** rightmost
child of a symbol with equal priority.

In C, binary operators are all left-associative, meaning that the expression 
`true && false && false` parses unambiguously as `(true && false) && false`,
because `&&` cannot appear as the rightmost child of itself.

Consider, then, the fourth iteration on the grammar of this definition
(`lesson-04-b.k`):

```k
module LESSON-04-B

  syntax Boolean ::= "true" | "false"
                   | "(" Boolean ")" [bracket]
                   > "!" Boolean [function]
                   > left: Boolean "&&" Boolean [function]
                   > left: Boolean "^" Boolean [function]
                   > left: Boolean "||" Boolean [function]

endmodule
```

Here each priority group, immediately after the `::=` or `>` operator, can
be followed by a symbol representing the associativity of that priority group:
either `left:` for left associativity, `right:` for right associativity, or
`non-assoc:` for non-associativity. In this example, each priority group we
apply associativity to has only a single production, but we could equally well
write a priority block with multiple productions and an associativity.

For example, consider the following, different grammar (`lesson-04-c.k`):

```k
module LESSON-04-C

  syntax Boolean ::= "true" | "false"
                   | "(" Boolean ")" [bracket]
                   > "!" Boolean [function]
                   > left: 
                     Boolean "&&" Boolean [function]
                   | Boolean "^" Boolean [function]
                   | Boolean "||" Boolean [function]

endmodule
```

In this example, unlike the one above, `&&`, `^`, and `||` have the same
priority. However, viewed as a group, the entire group is left associative.
This means that none of `&&`, `^`, and `||` can appear as the right child of
any of `&&`, `^`, or `||`. As a result of this, this grammar is also not
ambiguous. However, it expresses a different grammar, and you are encouraged
to think about what the differences are in practice.

### Exercise

Parse the program `true && false && false` yourself, and confirm that the AST
places the rightmost `&&` at the top of the expression. Then modify the 
definition to generate the alternative parse.

## Explicit priority and associativity declarations

Previously we have only considered the case where all of the productions
which you wish to express a priority or associativity relation over are
co-located in the same block of productions. However, in practice this is not
always feasible or desirable, especially as a definition grows in size across
multiple modules.

As a result of this, K provides a second way of declaring priority and
associativity relations.

Consider the following grammar, which we will name `lesson-04-d.k` and which
will express the exact same grammar as `lesson-04-b.k`

```k
module LESSON-04-D

  syntax Boolean ::= "true" [literal] | "false" [literal]
                   | "(" Boolean ")" [atom, bracket]
                   | "!" Boolean [not, function]
                   | Boolean "&&" Boolean [and, function]
                   | Boolean "^" Boolean [xor, function]
                   | Boolean "|" Boolean [or, function]

  syntax priorities literal atom > not > and > xor > or
  syntax left and
  syntax left xor
  syntax left or
endmodule
```

This introduces a couple of new features of K. First of all, we see a bunch of
attributes we don't already recognize. These are actually not built-in
attributes, but rather user-defined attributes that are used to group
productions together conceptually. For example, `literal` in the
`syntax priorities` sentence is used to refer to the productions with the
`literal` attribute, i.e., `true` and `false`.

Once we understand this, it becomes relatively straightforward to understand
the meaning of this grammar. Each `syntax priorities` sentence defines a
priority relation where each `>` separates a priority group containing all
the productions with at least one of the attributes in that group, and each
`syntax left`, `syntax right`, or `syntax non-assoc` sentence defines an
associativity relation connecting all the productions with one of the target
attributes together into a left-, right-, or non-associative grouping.

## Prefer/avoid

Sometimes priority and associativity prove insufficient to disambiguate a
grammar. In particular, sometimes it is desirable to be able to choose between
two ambiguous parses directly while still not rejecting any parses if the term
parsed is unambiguous. A good example of this is the famous "dangling else"
problem in imperative C-like languages.

Consider the following definition (`lesson-04-E.k`):

```k
module LESSON-04-E

  syntax Exp ::= "true" | "false"
  syntax Stmt ::= "if" "(" Exp ")" Stmt
                | "if" "(" Exp ")" Stmt "else" Stmt
                | "{" "}"
endmodule
```

We can write the following program (`dangling-else.if`):

```
if (true) if (false) {} else {}
```

This is ambiguous because it is unclear whether the `else` clause is part of
the outer `if` or the inner `if`. At first we might try to resolve this with
priorities, saying that the `if` without an `else` cannot appear as a child of
the `if` with an `else`. However, because the non-terminal in the parent symbol
is both preceded and followed by a terminal, this will not work.

Instead, we can resolve the ambiguity directly by telling the parser to
"prefer" or "avoid" certain productions when ambiguities arise. For example,
when we parse this program, we see the following ambiguity as an error message:

```
[Error] Inner Parser: Parsing ambiguity.
1: syntax Stmt ::= "if" "(" Exp ")" Stmt

`if(_)__LESSON-04-E_Stmt_Exp_Stmt`(`true_LESSON-04-E_Exp`(.KList),`if(_)_else__LESSON-04-E_Stmt_Exp_Stmt_Stmt`(`false_LESSON-04-E_Exp`(.KList),`;_LESSON-04-E_Stmt`(.KList),`;_LESSON-04-E_Stmt`(.KList)))
2: syntax Stmt ::= "if" "(" Exp ")" Stmt "else" Stmt

`if(_)_else__LESSON-04-E_Stmt_Exp_Stmt_Stmt`(`true_LESSON-04-E_Exp`(.KList),`if(_)__LESSON-04-E_Stmt_Exp_Stmt`(`false_LESSON-04-E_Exp`(.KList),`;_LESSON-04-E_Stmt`(.KList)),`;_LESSON-04-E_Stmt`(.KList))
        Source(./dangling-else.if)
        Location(1,1,1,30)
```

Roughly, we see that the ambiguity is between an `if` with an `else` or an `if`
without an `else`. Since we want to pick the first parse, we can tell K to
"avoid" the second parse with the `avoid` attribute. Consider the following
modified definition (`lesson-04-f.k`):

```k
module LESSON-04-F

  syntax Exp ::= "true" | "false"
  syntax Stmt ::= "if" "(" Exp ")" Stmt
                | "if" "(" Exp ")" Stmt "else" Stmt [avoid]
                | "{" "}"
endmodule
```

Here we have added the `avoid` attribute to the `else` production. As a result,
when an ambiguity occurs and one or more of the possible parses has that symbol
at the top of the ambiguous part of the parse, we remove those parses from
consideration and consider only those remaining. The `prefer` attribute behaves
similarly, but instead removes all parses which do not have that attribute.
In both cases, no action is taken if the parse is not ambiguous.

## Exercises

1. Parse the program `if (true) if (false) {} else {}` using `lesson-04-f.k`
and confirm that else clause is part of the innermost `if` statement. Then
modify the definition so that you will get the alternative parse.

2. Modify your solution from lesson 1.3, problem 2 so that unary negation should
bind tighter than multiplication and division, which should bind tighter than
addition and subtraction, and each binary operator should be left associative.
Write these priority and associativity declarations both inline and explicitly.

3. Write a simple grammar containing at least one ambiguity that cannot be
resolved via priority or associativity, and then use the `prefer` attribute to
resolve that ambiguity.

## Next lesson

Once you have completed the above exercises, you can continue to
[Lesson 1.5: Modules, Imports, and Requires](../05_modules/README.md).
