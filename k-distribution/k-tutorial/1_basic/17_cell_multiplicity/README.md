# Lesson 1.17: Cell Multiplicity and Cell Collections

The purpose of this lesson is to explain how you can create optional cells
and cells that repeat multiple times in a configuration using a feature called
**cell multiplicity**.

## Cell Multiplicity

K allows you to specify attributes for cell productions as part of the syntax
of configuration declarations. Unlike regular productions, which use the `[]`
syntax for attributes, configuration cells use an XML-like attribute syntax:

```
configuration <k color="red"> $PGM:K </k>
```

This configuration declaration gives the `<k>` cell the color red during
unparsing using the `color` attribute as discussed in
[Lesson 1.9](../09_unparsing/README.md).

However, in addition to the usual attributes for productions, there are some
other attributes that can be applied to cells with special meaning. One such
attribute is the `multiplicity` attribute. By default, each cell that is
declared occurs exactly once in every configuration term. However, using the
`multiplicity` attribute, this default behavior can be changed. There are two
values that this attribute can have: `?` and `*`.

## Optional cells

The first cell multiplicity we will discuss is `?`. Similar to a regular
expression language, this attribute tells the compiler that this cell can
appear 0 or 1 times in the configuration. In other words, it is an
**optional cell**. By default, K does not create optional cells in the initial
configuration, unless that optional cell has a configuration variable inside
it. However, it is possible to override the default behavior and create that
cell initially by adding the additional cell attribute `initial=""`.

K uses the `.Bag` symbol to represent the absence of any cells in a particular
rule. Consider the following module:

```k
module LESSON-17-A
  imports INT

  configuration <k> $PGM:K </k>
                <optional multiplicity="?"> 0 </optional>

  syntax KItem ::= "init" | "destroy"

  rule <k> init => . ...</k>
       (.Bag => <optional> 0 </optional>)
  rule <k> destroy => . ...</k>
       (<optional> _ </optional> => .Bag)

endmodule
```	

In this definition, when the `init` symbol is executed, the `<optional>` cell
is added to the configuration, and when the `destroy` symbol is executed, it
is removed. Any rule that matches on that cell will only match if that cell is
present in the configuration.

### Exercise

Create a simple definition with a `Stmts` sort that is a `List{Stmt,""}` and
a `Stmt` sort with the constructors
`syntax Stmt ::= "enable" | "increment" | "decrement" | "disable"`. The
configuration should have an optional cell that contains an integer that
is created with the `enable` command, destroyed with the `disable` command,
and its value is incremented or decremented by the `increment` and `decrement`
command.

## Cell collections

The second type of cell multiplicity we will discuss is `*`. Simlar to a
regular expression languiage, this attribute tells the compiler that this cell
can appear 0 or more times in the configuration. In other words, it is a
**cell collection**. All cell collections are required to have the `type`
attribute set to either `Set` or `Map`. A `Set` cell collection is represented
as a set and behaves internally the same as the `Set` sort, although it
actually declares a new sort. A `Map` cell collection is represented as a `Map`
in which the first subcell of the cell collection is the key and the remaining
cells are the value.

For example, consider the following module:

```k
module LESSON-17-B
  imports INT
  imports ID-SYNTAX

  syntax Stmt ::= Id "=" Exp ";" [strict(2)]
                | "return" Exp ";" [strict]
  syntax Stmts ::= List{Stmt,""}
  syntax Exp ::= Id 
               | Int 
               | Exp "+" Exp [seqstrict]
               | "spawn" "{" Stmts "}"
               | "join" Exp ";"

  configuration <threads>
                  <thread multiplicity="*" type="Map">
                    <id> 0 </id>
                    <k> $PGM:K </k>
                  </thread>
                </threads>
                <state> .Map </state>
                <next-id> 1 </next-id>

  rule <k> X:Id => I:Int ...</k>
       <state>... X |-> I ...</state>
  rule <k> X:Id = I:Int ; => . ...</k>
       <state> STATE => STATE [ X <- I ] </state>
  rule <k> S:Stmt Ss:Stmts => S ~> Ss ...</k>
  rule <k> I1:Int + I2:Int => I1 +Int I2 ...</k>

  rule <thread>...
         <k> spawn { Ss } => NEXTID </k>
       ...</thread>
       <next-id> NEXTID => NEXTID +Int 1 </next-id>
       (.Bag => 
       <thread>
         <id> NEXTID </id>
         <k> Ss </k>
       </thread>)

  rule <thread>...
         <k> join ID:Int ; => I ...</k>
       ...</thread>
       (<thread>
         <id> ID </id>
         <k> return I:Int ; ...</k>
       </thread> => .Bag)

  syntax Bool ::= isKResult(K) [function, symbol]
  rule isKResult(_:Int) => true
  rule isKResult(_) => false [owise]
endmodule
```

This module implements a very basic fork/join semantics. The `spawn` expression
spawns a new thread to execute a sequence of statements and returns a thread
id, and the `join` statement waits until a thread executes `return` and then
returns the return value of the thread.

Note something quite novel here: the `<k>` cell is inside a cell of
multiplicity `*`. Since the `<k>` cell is just a regular cell (mostly), this
is perfectly allowable. Rules that don't mention a specific thread are
automatically completed to match any thread.

When you execute programs in this language, the cells in the cell collection
get sorted and printed like any other collection, but they still display like
cells. Rules in this language also benefit from all the structural power of
cells, allowing you to omit cells you don't care about or complete the
configuration automatically. This allows you to have the power of cells while
still being a collection under the hood.

## Exercises

1. Modify the solution from Lesson 1.16, Problem 1 so that the cell you use to
keep track of functions in a `Map` is now a cell collection. Run some programs
and compare how they get unparsed before and after this change.

## Next lesson

Once you have completed the above exercises, you can continue to
[Lesson 1.18: Term Equality and the Ternary Operator](../18_equality_and_conditionals/README.md).
