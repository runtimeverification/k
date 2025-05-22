---
copyright: Copyright (c) Runtime Verification, Inc. All Rights Reserved.
---

# Lesson 1.4: Disambiguating Parses

In this lesson you will learn how to disambiguate a grammar by using K's 
built-in features, rather than _artificial_ operators such as brackets. 
You will learn how to define a precedence order on operators and 
associativity directions for them.

## Priority blocks

Parsing unambiguous languages is asymptotically faster than parsing ambiguous
languages. That's why in practice, very few formal languages outside the domain
of natural language processing are ambiguous.

Cluttering the code with brackets to remove ambiguity is not an ideal solution. 
Instead, programming language designers have developed methods for 
disambiguating language expressions by making use of operator precedence and 
associativity directions for them. It is often possible to remove _all_ 
ambiguities in a grammar with these methods, as they instruct the parser to 
accept some ASTs in favor of others.

In general, grammars can be rewritten to remove unwanted parses. However,
in K, the grammar specification and AST generation are intrinsically linked,
so we discourage this approach. You will still learn how remove unwanted parses 
in K towards the end of this lesson. Now we continue with showing you how to
explicitly express the relative precedence of operators in different 
situations in order to resolve grammar ambiguity.

Recall that in C, `&&` binds tighter than `||`, meaning that it has higher
precedence, meaning additionally that the expression `true && false || false` 
has only one valid AST: `(true && false) || false`.

Consider, then, the third iteration on the grammar of Boolean expressions and
save the code below in file `lesson-04-a.k`:

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

In this example, some of the pipe symbols `|` separating productions have been 
replaced with `>`. This serves to describe the **priority groups** associated 
with a block of productions. The first priority group consists of the atoms 
of the language: `true`, `false`, and the bracket operator. In general, a 
priority group starts either at the `::=` or `>` operator and extends until 
either the next `>` operator, or the end of the production block. Thus, we can 
see that the second, third, fourth, and fifth priority groups in this grammar 
all consist of a single production.

The meaning of these priority groups becomes apparent when parsing programs:
A symbol with a **lesser priority**, (i.e., one that **binds looser**), cannot
appear as the **direct child** of a symbol with a **greater priority** (i.e.,
one that **binds tighter**). In this case, the `>` operator can be seen as a
**greater-than** operator describing a transitive partial ordering on the
productions in the production block, expressing their relative priority.

To see this more concretely, let's look again at the program
`true && false || false`. As noted before, this program was ambiguous because 
the parser could either choose `&&` to be the child of `||` or vice versa. 
Recall figures 3-A and 3-B in previous lesson. However, because a symbol 
with lesser priority (i.e., `||`) cannot appear as the _direct_ child of a 
symbol with greater priority (i.e., `&&`), the parser will **reject** the 
parse where `||` is under the `&&` operator (Fig. 3-B). As a result, we are 
left with the unambiguous parse `(true && false) || false`. Conversely, if 
the user wants the other parse, they can express this with brackets by 
explicitly writing `true && (false || false)`. This still parses successfully because the
`||` operator is no longer the **direct** child of the `&&` operator, but of
`()` operator, even if the bracket is not explicitly depicted in the AST.
Internally, `&&` operator is viewed as an **indirect** parent, which is not 
subject to the priority restriction.

You must have noticed that `()` has been defined as having greater priority
than `||` and we might have possibly reached a contradiction as `||` cannot 
appear as a direct child of `()`. What we have not mentioned is that the
priority rule is more complex and applies only _conditionally_. Specifically, 
it applies in cases where the first child is either the first or last 
production item in the parent's production. For example, in production 
`Boolean "&&" Boolean`, the first `Boolean` non-terminal is not preceded by 
any terminals, and the last `Boolean` is not followed by any terminals. As a 
result, we apply the priority rule to both children of `&&`.
In production `"(" Boolean ")"`, the non-terminal is both preceded and followed
by terminals `"("` and `")"`. Thus, the priority rule does apply when `()` is 
the parent. Because of this, program `true && (false || false)` parses 
successfully.

### Exercise

Parse the program `true && false || false` using `kast`, and confirm that the 
AST places `||` as the top-level symbol. Then modify the definition so that you
will get the alternative parse.

## Associativity

Sometimes, even after breaking the expression grammar into priority blocks we 
still get an ambiguous grammar. Let's try to parse the following program 
(`assoc.bool`):

```
true && false && false
```

Priority blocks will not help us here. We have two possible parses with a
direct parent and child which are within a single priority block (in this case, 
`&&` is in the same block as itself):

Fig. 4-A
```
         &&
       /    \
     &&    false
   /    \
true   false
```

Fig. 4-B
```
    &&
  /    \
true    &&              
      /    \
   false  false    
```

This is where the notion of associativity comes into play. Associativity
applies the following additional rules to parses:

* a left-associative symbol cannot appear as a direct rightmost child of a
symbol with equal priority;
* a right-associative symbol cannot appear as a direct leftmost child of a
symbol with equal priority; and
* a non-associative symbol cannot appear as a direct leftmost **or** rightmost
child of a symbol with equal priority.

In C, binary operators are all left-associative, meaning that expression
`true && false && false` parses unambiguously as `(true && false) && false`,
because `&&` cannot appear as the rightmost child of itself, only the AST 
in Fig. 4-A is valid.

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
be followed by a literal representing the associativity of that priority group:
either `left:` for left-associativity, `right:` for right-associativity, or
`non-assoc:` for non-associativity. In this example, each priority group we
apply associativity to has only a single production, but we could equally well
write a priority block with multiple productions and one associativity.
For example, consider the grammar below (file `lesson-04-c.k`):

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
priority, as are part of the same block. Addionally, the entire group is 
left-associative. This means that none of `&&`, `^`, and `||` can appear as the 
right child of any of `&&`, `^`, or `||`. Hence, this grammar is also not 
ambiguous. However, it expresses a different grammar, and you are encouraged
to think about what the differences are in practice.

### Exercise

Parse the program `true && false && false` yourself, and confirm that the AST
places the rightmost `&&` at the top of the expression. Then modify the
definition to generate the alternative parse.

## Explicit priority and associativity declarations

Previously we have only considered the case where all productions expressing a 
priority or associativity relation are co-located in the same block of 
productions. However, in practice this is not always feasible or desirable, 
especially as a definition grows in size across multiple modules. As a result, 
K provides a second way of declaring priority and associativity relations.

Consider the following grammar, which we name `lesson-04-d.k` and which 
expresses the exact same grammar as `lesson-04-b.k`:

```k
module LESSON-04-D

  syntax Boolean ::= "true" [group(literal)] | "false" [group(literal)]
                   | "(" Boolean ")" [group(atom), bracket]
                   | "!" Boolean [group(not), function]
                   | Boolean "&&" Boolean [group(and), function]
                   | Boolean "^" Boolean [group(xor), function]
                   | Boolean "||" Boolean [group(or), function]

  syntax priority literal atom > not > and > xor > or
  syntax left and
  syntax left xor
  syntax left or
  
endmodule
```

This introduces a couple of new features of K. First, the `group(_)` attribute
of a production is used to conceptually group together sets of sentences under 
a common user-defined name. For example, `literal` in the `syntax priority` 
sentence is used to refer to all productions marked with the `group(literal)` 
attribute, i.e., `true` and `false`, `atom` to all productions marked with 
`group(atom)`, i.e., braket production, and so on and so fort. A production can 
belong to multiple groups using syntax such as `group(myGrp1,myGrp2)`.

Once we understand this, it becomes relatively straightforward to understand
the meaning of this grammar. Each `syntax priority` sentence defines a priority 
relation where `>` separates different priority groups. Each priority group is 
defined by a list of one or more group names, and consists of all productions 
which are members of at least one of those named groups. `literal` and `atom` 
are only separated by space as they have the same precedence.

In the same way, sentences `syntax left`, `syntax right`, or `syntax non-assoc` 
define an associativity relation among left-, right-, or non-associative
groups, respectively. Specifically, this means that:

```
syntax left a b
```

is _different_ to:

```
syntax left a
syntax left b
```

`syntax left a b` places `a` and `b` in the same associativity block, meaning
that `a` and/or `b` cannot be the rightmost child of `a` and/or `b`. The latter
sentences don't define this restriction, as `a` and `b` are not part of the
same group.

As a consequence, `syntax [left|right|non-assoc]` should not be used to
group together labels with different priority.

## Prefer/avoid productions

Sometimes priority and associativity prove insufficient to disambiguate a
grammar. In particular, sometimes it is desirable to be able to choose between
two ambiguous parses directly while still not rejecting any parses if the term
parsed is unambiguous. A good example of this is the famous "dangling else"
problem in imperative C-like languages.

Consider the following definition (`lesson-04-e.k`):

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
priorities, specifying that the `if` without an `else` cannot appear as a child 
of the `if` with an `else`. However, because the non-terminal in the parent 
symbol is both preceded and followed by a terminal, this will not work.

Instead, we can resolve the ambiguity directly by telling the parser to
"prefer" or "avoid" certain productions when ambiguities arise. For example,
when we parse this program with

```
kompile lesson-04-e.k
kast --output kore dangling-else.if
```

we get the following ambiguity as an error message, minus the formatting:

```
[Error] Inner Parser: Parsing ambiguity.
1: syntax Stmt ::= "if" "(" Exp ")" Stmt
    `if(_)__LESSON-04-E_Stmt_Exp_Stmt`(
      `true_LESSON-04-E_Exp`(.KList),
      `if(_)_else__LESSON-04-E_Stmt_Exp_Stmt_Stmt`(
        `false_LESSON-04-E_Exp`(.KList),
        `{}_LESSON-04-E_Stmt`(.KList),
        `{}_LESSON-04-E_Stmt`(.KList)
      )
    )

2: syntax Stmt ::= "if" "(" Exp ")" Stmt "else" Stmt
    `if(_)_else__LESSON-04-E_Stmt_Exp_Stmt_Stmt`(
      `true_LESSON-04-E_Exp`(.KList),
      `if(_)__LESSON-04-E_Stmt_Exp_Stmt`(
        `false_LESSON-04-E_Exp`(.KList),
        `{}_LESSON-04-E_Stmt`(.KList)
      ),
      `{}_LESSON-04-E_Stmt`(.KList)
    )

	Source(./dangling-else.if)
	Location(1,1,1,32)
	1 |	if (true) if (false) {} else {}
	  .	^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
```

Roughly, we see that the ambiguity is between an `if` with an `else` or an `if`
without an `else`. Since we want to pick the first parse, we can tell K to
**avoid** the second parse with the `avoid` attribute. Consider the following
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
when an ambiguity occurs and any of the possible parses has that symbol at the 
top of the ambiguous part of the parse, we discard those parses, and consider
only the remaining ones. The `prefer` attribute behaves similarly, but instead 
removes all parses which do not have that attribute. In both cases, no action 
is taken if the parse is not ambiguous.

If we parse the program in `dangling-else.if` with this grammar,

```
kompile lesson-04-f.k
kast --output kast dangling-else.if
```

we get the following output, minus the formatting:

```
`if(_)__LESSON-04-F_Stmt_Exp_Stmt`(
	`true_LESSON-04-F_Exp`(.KList),
	`if(_)_else__LESSON-04-F_Stmt_Exp_Stmt_Stmt`(
		`false_LESSON-04-F_Exp`(.KList),
		`{}_LESSON-04-F_Stmt`(.KList),
		`{}_LESSON-04-F_Stmt`(.KList)
	)
)
```

As we expected, the AST where the `else` corresponds to the first `if` is 
discarded.


## Exercises

1. Parse the program `if (true) if (false) {} else {}` using `lesson-04-f.k`
and confirm that the `else` clause is part of the innermost `if` statement. 
Then modify the definition so that you will get the alternative parse.

2. Modify your solution from Lesson 1.3, Exercise 2 so that unary negation should
bind tighter than multiplication and division, which should bind tighter than
addition and subtraction, and each binary operator should be left associative.
Write these priority and associativity declarations explicitly, and then
try to write them inline.

3. Write a simple grammar containing at least one ambiguity that cannot be
resolved via priority or associativity, and then use the `prefer` attribute to
resolve that ambiguity.

4. Explain why the following grammar is not labeled ambiguous by the K parser 
when parsing `abb`, then make the parser realize the ambiguity.

```k
module EXERCISE4

  syntax Expr ::= "a" Expr "b"
                | "abb"
                | "b"

endmodule
```

## Next lesson

Once you have completed the above exercises, you can continue to
[Lesson 1.5: Modules, Imports, and Requires](../05_modules/README.md).
