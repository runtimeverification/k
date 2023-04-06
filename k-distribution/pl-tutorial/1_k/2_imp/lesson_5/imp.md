---
copyright: Copyright (c) K Team. All Rights Reserved.
---

IMP
===

Author: Grigore Roșu (grosu@illinois.edu)  
Organization: University of Illinois at Urbana-Champaign

### Abstract
This is the **K** semantic definition of the classic IMP language.
IMP is considered a folklore language, without an official inventor,
and has been used in many textbooks and papers, often with slight
syntactic variations and often without being called **IMP**.  It includes
the most basic imperative language constructs, namely basic constructs
for arithmetic and Boolean expressions, and variable assignment,
conditional, while loop and sequential composition constructs for statements.

```k
module IMP-SYNTAX
  imports DOMAINS-SYNTAX
```
### Syntax
This module defines the syntax of **IMP**.
Note that `<=` is sequentially strict, and `&&` is strict only in its first
argument, because we want to give it a short-circuit semantics.

```k
  syntax AExp  ::= Int | Id
                 | "-" Int                    [format(%1%2)]
                 | AExp "/" AExp              [left, strict, color(pink)]
                 | "(" AExp ")"               [bracket]
                 > AExp "+" AExp              [left, strict, color(pink)]
  syntax BExp  ::= Bool
                 | AExp "<=" AExp             [seqstrict, latex({#1}\leq{#2}), color(pink)]
                 | "!" BExp                   [strict, color(pink)]
                 | "(" BExp ")"               [bracket]
                 > BExp "&&" BExp             [left, strict(1), color(pink)]
  syntax Block ::= "{" "}"
                 | "{" Stmt "}"               [format(%1%i%n%2%d%n%3)]
  syntax Stmt  ::= Block
                 | Id "=" AExp ";"            [strict(2), color(pink), format(%1 %2 %3%4)]
                 | "if" "(" BExp ")"
                   Block "else" Block         [strict(1), colors(yellow, white, white, yellow), format(%1 %2%3%4 %5 %6 %7)]
                 | "while" "(" BExp ")" Block [colors(yellow,white,white), format(%1 %2%3%4 %5)]
                 > Stmt Stmt                  [left, format(%1%n%2)]
```
An IMP program declares a set of variables and then executes a
statement in the state obtained after initializing all those variables
to 0. **K** provides builtin support for generic syntactic lists:
`List{Nonterminal,terminal}` stands for `terminal`-separated lists of `Nonterminal` elements.

```k
  syntax Pgm ::= "int" Ids ";" Stmt           [format(%1 %2%3%n%4), colors(yellow,pink)]
  syntax Ids ::= List{Id,","}                 [format(%1%2 %3)]
endmodule
```

We are done with the definition of IMP's syntax.  Make sure
that you write and parse several interesting programs before you move to the
semantics.

```k
module IMP
  imports IMP-SYNTAX
  imports DOMAINS
```
### Semantics
This module defines the semantics of **IMP**.
Before you start adding semantic rules to a **K** definition, you need to
define the basic semantic infrastructure consisting of definitions for
`results` and the `configuration`.

### Values and results
IMP only has two types of values, or results of computations: integers
and Booleans.  We here use the **K** builtin variants for both of them.

```k
  syntax KResult ::= Int | Bool
```

### Configuration
The configuration of IMP is trivial: it only contains two cells, one
for the computation and another for the state.  For good encapsulation
and clarity, we place the two cells inside another cell, the *top* cell
which is labeled `T`.

```k
  configuration <T color="yellow">
                  <k color="green"> $PGM:Pgm </k>
                  <state color="red"> .Map </state>
                </T>
```

The configuration variable *PGM* tells the **K** tool where to
place the program.  More precisely, the command
`krun program` parses the program and places the resulting
**K** abstract syntax tree in the `k` cell before invoking the
semantic rules described in the sequel.  The `.` in the
`state` cell, written `.Map` in ASCII in the
`imp.md` file, is **K**'s way to say *nothing*. Technically, it
is a constant which is the unit, or identity, of all maps in **K**
(similar dot units exist for other **K** structures, such as lists, sets,
multi-sets, etc.).

### Arithmetic expressions
The **K** semantics of each arithmetic construct is defined below.

### Variable lookup
A program variable `X` is looked up in the state by matching a binding
of the form `X |-> I` in the state cell. If such a binding does not
exist, then the rewriting process will get stuck. Thus our semantics of
IMP disallows uses of uninitialized variables.  Note that the variable
to be looked up is the first task in the `k` cell (the cell is
closed to the left and torn to the right), while the binding can be
anywhere in the `state` cell (the cell is torn at both sides).

```k
  rule <k> X:Id => I ...</k> <state>... X |-> I ...</state>
```

### Arithmetic operators
There is nothing special about these, but recall that **K**'s configuration
abstraction mechanism is at work here!  That means that the rewrites in the
rules below all happen at the beginning of the `k` cell.

```k
  rule I1 / I2 => I1 /Int I2  requires I2 =/=Int 0
  rule I1 + I2 => I1 +Int I2
  rule - I1 => 0 -Int I1
```

### Boolean expressions
The rules below are straightforward.  Note the short-circuited semantics
of `&&`; this is the reason we annotated the syntax of
`&&` with the **K** attribute `strict(1)` instead of `strict`.

```k
  rule I1 <= I2 => I1 <=Int I2
  rule ! T => notBool T
  rule true && B => B
  rule false && _ => false
```

### Blocks and Statements
There is one rule per statement construct except for the conditional,
which needs two rules.

### Blocks
The empty block `{}` is simply dissolved.  The `.` below is the
unit of the computation list structure `K`, that is, the empty task.
Similarly, the non-empty blocks are dissolved and replaced by their statement
contents, thus effectively giving them a bracket semantics; we can afford to
do this only because we have no block-local variable declarations yet in IMP.
Since we tagged the rules below as *structural*, the **K** tool structurally
erases the block constructs from the computation structure, without
considering their erasure as computational steps in the resulting transition
systems.  You can make these rules computational (dropping the attribute
`structural`) if you do want these to count as computational steps.

```k
  rule {} => .   [structural]
  rule {S} => S  [structural]
```

### Assignment
The assigned variable is updated in the state.  The variable is expected
to be declared, otherwise the semantics will get stuck.  At the same time,
the assignment is dissolved.

```k
  rule <k> X = I:Int; => . ...</k> <state>... X |-> (_ => I) ...</state>
```

### Sequential composition
Sequential composition is simply structurally translated into **K**'s
builtin task sequentialization operation.  You can make this rule
computational (i.e., remove the `structural` attribute) if you
want it to count as a computational step.  Recall that the semantics
of a program in a programming language defined in **K** is the transition
system obtained from the initial configuration holding that program
and counting only the steps corresponding to computational rules as
transitions (i.e., hiding the structural rules as unobservable, or
internal steps).

```k
  rule S1:Stmt S2:Stmt => S1 ~> S2  [structural]
```

### Conditional
The conditional statement has two semantic cases, corresponding to
when its condition evaluates to `true` or to `false`.
Recall that the conditional was annotated with the attribute
`strict(1)` in the syntax module above, so only its first
argument is allowed to be evaluated.

```k
  rule if (true)  S else _ => S
  rule if (false) _ else S => S
```

### While loop
We give the semantics of the `while` loop by unrolling.
Note that we preferred to make the rule below structural.

```k
  rule while (B) S => if (B) {S while (B) S} else {}  [structural]
```

### Programs
The semantics of an IMP program is that its body statement is executed
in a state initializing all its global variables to 0.  Since **K**'s
syntactic lists are internally interpreted as cons-lists (i.e., lists
constructed with a head element followed by a tail list), we need to
distinguish two cases, one when the list has at least one element and
another when the list is empty.  In the first case we initialize the
variable to 0 in the state, but only when the variable is not already
declared (all variables are global and distinct in IMP).  We prefer to
make the second rule structural, thinking of dissolving the residual
empty `int;` declaration as a structural cleanup rather than as
a computational step.

```k
  rule <k> int (X,Xs => Xs);_ </k> <state> Rho:Map (.Map => X|->0) </state>
    requires notBool (X in keys(Rho))
  rule int .Ids; S => S  [structural]
endmodule
```
