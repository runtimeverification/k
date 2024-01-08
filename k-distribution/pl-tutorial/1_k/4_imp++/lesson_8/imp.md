---
copyright: Copyright (c) Runtime Verification, Inc. All Rights Reserved.
---

IMP++
=====

Author: Grigore Roșu (grosu@illinois.edu)  
Organization: University of Illinois at Urbana-Champaign

### Abstract
This is the **K** semantic definition of the IMP++ language.
IMP++ extends the IMP language with the features listed below. We
strongly recommend you to first familiarize yourself with the IMP
language and its **K** definition in Tutorial 2 before proceeding.

__Strings and concatenation of strings.__ Strings are useful
for the `print` statement, which is discussed below. For
string concatenation, we use the same `+` construct that we use
for addition (so we overload it).

__Variable increment.__ We only add a pre-increment construct:
`++x` increments variable `x` and evaluates to the
incremented value. Variable increment makes the evaluation of
expressions have side effects, and thus makes the evaluation strategies
of the various language constructs have an influence on the set
of possible program behaviors.

__Input and output.__ IMP++ adds a `read()` expression
construct which reads an integer number and evaluates to it, and
a variadic (i.e., it has an arbitrary number of arguments) statement
construct `print(e1,e2,...,en)` which evaluates its arguments
and then outputs their values. Note that the **K** tool allows to
connect the input and output cells to the standard input and output
buffers, this way compiling the language definition into an
interactive interpreter.

__Abrupt termination.__ The `halt` statement simply halts
the program. The **K** tool shows the resulting configuration, as if the
program terminated normally. We therefore assume that an external
observer does not care whether the program terminates normally or
abruptly, same like with `exit` statements in conventional
programming languages like C.

__Dynamic threads.__ The expression construct `spawn s`
starts a new concurrent thread that executes statement `s`,
which is expected to be a block, and evaluates immediately to a fresh
thread identifier that is also assigned to the newly created thread.
The new thread is given at creation time the `environment` of its
parent, so it can access all its parent's variables. This allows for
the parent thread, and the child thread to communicate; it also allows
for races and "unexpected" behaviors, so be careful.
For thread synchronization, IMP++ provides a thread join statement
construct `join t;`, where `t` evaluates to a thread
identifier, which stalls the current thread until thread `t`
completes its computation. For simplicity, we here assume a
sequentially consistent shared memory model. To experiment with other
memory models, see the definition of KERNELC.

__Blocks and local variables.__ IMP++ allows blocks enclosed by
curly brackets. Also, IMP's global variable declaration construct is
generalized to be used anywhere as a statement, not only at the
beginning of the program. As expected, the scope of the declared
variables is from their declaration point till the end of the most
nested enclosing block.


### What You Will Learn Here


* How to define a less trivial language in **K**, as explained above.
* How to use the `superheat` and `supercool`
options of the **K** tool `kompile` to exhaustively explore the
non-determinism due to underspecified evaluation strategies.
* How to use the `transition` option of the **K** tool to
exhaustively explore the non-determinism due to concurrency.
* How to connect certain cells in the configuration to the
standard input and standard output, and thus turn the `krun`
tool into an interactive interpreter for the defined language.
* How to exhaustively search for the non-deterministic behaviors
of a program using the `search` option of `krun`.

```k
module IMP-SYNTAX
  imports DOMAINS-SYNTAX
```
### Syntax
IMP++ adds several syntactic constructs to IMP. Also, since the
variable declaration construct is generalized to be used anywhere a
statement can be used, not only at the beginning of the program, we
need to remove the previous global variable declaration of IMP and
instead add a variable declaration statement construct

We do not re-discuss the constructs which are taken over from IMP,
except when their syntax has been subtly modified (such as, for
example, the syntax of the previous "statement" assignment which
is now obtained by composing the new assignment expression, and the
new expression statement constructs); go the last lesson of
Tutorial 2 if you are interested in IMP's constructs. For execution
purposes, we tag the addition and division operations as members of the
`addition` and `division` groups. These groups have no theoretical significance,
in that they do not affect the semantics of the language in any way. They only
have practical relevance, specific to our implementation of the **K** tool.
Specifically, we can tell the **K** tool (using its `superheat` and `supercool`
options) that we want to exhaustively explore all the non-deterministic
behaviors (due to strictness) of these language constructs. For performance
reasons, by default the **K** tool chooses an arbitrary but fixed order to
evaluate the arguments of the strict language constructs, thus possibly losing
behaviors due to missed interleavings. This aspect was irrelevant in IMP,
because its expressions had no side effects, but it becomes relevant in IMP++.

The syntax of the IMP++ constructs is self-explanatory. Note that assignment
is now an expression construct. Also, `print` is variadic, taking a
list of expressions as argument. It is also strict, which means that the
entire list of expressions, that is, each expression in the list, will be
evaluated. Note also that we have now defined sequential composition
of statements as a whitespace-separated list of statements, aliased with
the nonterminal `Stmts`, and block as such a (possibly empty) sequence
of statements surrounded by curly brackets.

```k
  syntax AExp  ::= Int | String | Id
                 | "++" Id
                 | "read" "(" ")"
                 | "-" AExp                   [strict]
                 | "(" AExp ")"               [bracket]
                 > AExp "/" AExp              [left, strict, group(division)]
                 > AExp "+" AExp              [left, strict]
                 > "spawn" Block
                 > Id "=" AExp                [strict(2)]
  syntax BExp  ::= Bool
                 | AExp "<=" AExp             [seqstrict, latex({#1}\leq{#2})]
                 | "!" BExp                   [strict]
                 | "(" BExp ")"               [bracket]
                 > BExp "&&" BExp             [left, strict(1)]
  syntax Block ::= "{" Stmts "}"
  syntax Stmt  ::= Block
                 | AExp ";"                   [strict]
                 | "if" "(" BExp ")"
                   Block "else" Block         [strict(1)]
                 | "while" "(" BExp ")" Block
                 | "int" Ids ";"
                 | "print" "(" AExps ")" ";"
                 | "halt" ";"
                 > "join" AExp ";"            [strict]

  syntax Ids   ::= List{Id,","}               [klabel(exps)]
  syntax AExps ::= List{AExp,","}             [klabel(exps)]
  syntax Stmts ::= List{Stmt,""}
  syntax AExps ::= Ids
endmodule


module IMP
  imports IMP-SYNTAX
  imports DOMAINS
```

### Semantics
We next give the semantics of IMP++. We start by first defining its
configuration.

#### Configuration
The original configuration of IMP has been extended to include
all the various additional cells needed for IMP++.
To facilitate the semantics of threads, more specifically
to naturally give them access to their parent's variables, we prefer a
(rather conventional) split of the program state into an
`environment` and a `store`. An environment maps
variable names into `locations`, while a store maps locations
into values. Stores are also sometimes called `states`, or
`heaps`, or `memory`, in the literature. Like values, locations
can be anything. For simplicity, here we assume they are natural
numbers. Moreover, each thread has its own environment, so it knows
where all the variables that it has access to are located in the store
(that includes its locally declared variables as well as the variables
of its parent thread), and its own unique identifier. The store is
shared by all threads. For simplicity, we assume a sequentially consistent
memory model in IMP++. Note that the `thread` cell has multiplicity
`*`, meaning that there could be zero, one, or more instances of that cell
in the configuration at any given time. This multiplicity information
is important for **K**'s _configuration abstraction_ process: it tells
**K** how to complete rules which, in order to increase the modularity of the
definition, choose to not mention the entire configuration context.
The `in` and `out` cells hold the input and the output
buffers as lists of items.

```k
  configuration <T color="yellow">
                  <threads color="orange">
                    <thread multiplicity="*" color="blue" type="Map">
                      <id color="black"> 0 </id>
                      <k color="green"> $PGM:Stmts </k>
                      <env color="LightSkyBlue"> .Map </env>
                    </thread>
                  </threads>
//                <br/>
                  <store color="red"> .Map </store>
//                  <input color="magenta"> .List </input>
//                  <output color="Orchid"> .List </output>
                  <input color="magenta" stream="stdin"> .List </input>
                  <output color="Orchid" stream="stdout"> .List </output>
                </T>
// Replace the <input/> and <output/> cells with the next two in order to
// initialize the input buffer through krun
//     <input color="magenta"> $IN:List </input>
//     <output color="Orchid"> .List </output>
// Replace the <input/> and <output/> cells with the next two to connect the
// input/output buffers to stdin/stdout through krun
//     <input color="magenta" stream="stdin"> .List </input>
//     <output color="Orchid" stream="stdout"> .List </output>
// Replace the <input/> and <output/> cells with the next two to connect the
// input/output buffers to stdin/stdout and also allow input through krun
//     <input color="magenta" stream="stdin"> $IN:List </input>
//     <output color="Orchid" stream="stdout"> .List </output>
```

We can also use configuration variables to initialize
the configuration through `krun`. For example, we may want to
pass a few list items in the `in` cell when the program makes
use of `read()`, so that the semantics does not get stuck.
Recall from IMP that configuration variables start with a _$_
character when used in the configuration (see, for example,
_$PGM_) and can be initialized with any string by
`krun`; or course, the string should parse to a term of the
corresponding sort, otherwise errors will be generated.
Moreover, **K** allows you to connect list cells to the standard input or
the standard output. For example, if you add the attribute
`stream="stdin"` to the `in` cell, then `krun`
will prompt the user to pass input when the `in` cell is empty
and any semantic rule needs at least one item to be present there in
order to match. Similarly but dually, if you add the attribute
`stream="stdout"` to the `out` cell, then any item
placed into this cell by any rule will be promptly sent to the
standard output. This way, `krun` can be used to obtain
interactive interpreters based directly on the **K** semantics of the
language. For example:

```shell script
sh$ krun sum-io.imp --output none
Add numbers up to (<= 0 to quit)? 10
Sum = 55
Add numbers up to (<= 0 to quit)? 1000
Sum = 500500
Add numbers up to (<= 0 to quit)? 0
sh$
```

The option `--output none` instructs `krun` to not
display the resulting configuration after the program executes. The
input/output streaming works with or without this option, although
if you don't use the option then a configuration with empty
`in` and `out` cells will be displayed after the program
is executed. You can also initialize the configuration using
configuration variables and stream the contents of the cells to
standard input/output at the same time. For example, if you use a
configuration variable in the `in` cell and pass contents to it
through `krun`, then that contents will be first consumed and
then the user will be prompted to introduce additional input if the
program's execution encounters more `read()` constructs.

### The old IMP constructs
The semantics of the old IMP constructs is almost identical to their
semantics in the original IMP language, except for those constructs
making use of the program state and for those whose syntax has slightly
changed. Indeed, the rules for variable lookup and assignment in IMP
accessed the `state` cell, but that cell is not available in IMP++
anymore. Instead, we have to use the combination of environment and store
cells. Thanks to **K**'s implicit configuration abstraction, we do not have
to mention the `thread` and `threads` cells: these are
automatically inferred (and added by the **K** tool at compile time) from the
definition of the configuration above, as there is only one correct
way to complete the configuration context of these rules in order to
match the configuration declared above. In our case here, "correct way"
means that the `k` and `env` cells will be considered as
being part of the same `thread` cell, as opposed to each being part
of a different thread. Configuration abstraction is crucial for modularity,
because it gives us the possibility to write our definitions in a way that
may not require us to revisit existing rules when we change the configuration.
Changes in the configuration are quite frequent in practice, typically
needed in order to accommodate new language features. For example,
imagine that we initially did not have threads in IMP++. There
would be no need for the `thread` and `threads` cells in
the configuration then, the cells `k` and `env` being simply
placed at the top level in the `T` cell, together with the
already existing cells. Then the rules below would be exactly the
same. Thus, configuration abstraction allows you to not have to
modify your rules when you make structural changes in your language
configuration.

Below we list the semantics of the old IMP constructs, referring the
reader to the **K** semantics of IMP for their meaning. Like we tagged the
addition and the division rules above in the syntax, we also tag the lookup
and the assignment rules below (as members of the groups `lookup` and
`assignment`), because we want to refer to them when we generate the
language model (with the `kompile` tool), basically to allow them to
generate (possibly non-deterministic) transitions. Indeed, these two rules,
unlike the other rules corresponding to old IMP constructs, can yield
non-deterministic behaviors when more threads are executed concurrently.
In terms of rewriting, these two rules can "compete" with each other on
some program configurations, in the sense that they can both match at the
same time and different behaviors may be obtained depending upon which of
them is chosen first.

```k
  syntax KResult ::= Int | Bool
```
### Variable lookup

```k
  rule <k> X:Id => I ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> I ...</store>  [group(lookup)]
```

### Arithmetic constructs

```k
  rule I1 / I2 => I1 /Int I2  when I2 =/=Int 0
  rule I1 + I2 => I1 +Int I2
  rule - I => 0 -Int I
```

### Boolean constructs

```k
  rule I1 <= I2 => I1 <=Int I2
  rule ! T => notBool T
  rule true && B => B
  rule false && _ => false
```

### Variable assignment
Note that the old IMP assignment statement `X = I;` is now composed of two
constructs: an assignment expression construct `X = I`, followed by a
semicolon `;` turning the expression into a statement. The rationale behind
this syntactic restructuring has been explained in Lesson 7. Here is the
semantics of the two constructs:

```k
  rule _:Int; => .
  rule <k> X = I:Int => I ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> (_ => I) ...</store>  [group(assignment)]
```

### Sequential composition
Sequential composition has been defined as a whitespace-separated syntactic
list of statements. Recall that syntactic lists are actually syntactic
sugar for cons-lists. Therefore, the following two rules eventually
sequentialize a syntactic list of statements `s1 s2 ... sn..` into the
corresponding computation `s1 ~> s2 ~> ... ~> sn`.

```k
   rule .Stmts => .
   rule S:Stmt Ss:Stmts => S ~> Ss
```

### Conditional statement

```k
  rule if (true)  S else _ => S
  rule if (false) _ else S => S
```

### While loop
The only thing to notice here is that the empty block has been replaced
with the block holding the explicit empty sequence. That's because in
the semantics all empty lists become explicit corresponding dots
(to avoid parsing ambiguities)

```k
  rule while (B) S => if (B) {S while (B) S} else {.Stmts}
```

### The new IMP++ constructs
We next discuss the semantics of the new IMP++ constructs.

### Strings
First, we have to state that strings are also results.
Second, we give the semantics of IMP++ string concatenation (which
uses the already existing addition symbol `+` from IMP) by
reduction to the built-in string concatenation operation.

```k
  syntax KResult ::= String
  rule Str1 + Str2 => Str1 +String Str2
```

### Variable increment
Like variable lookup, this is also meant to be a supercool transition: we
want it to count both in the non-determinism due to strict operations above
it in the computation and in the non-determinism due to thread
interleavings. This rule also relies on **K**'s configuration abstraction.
Without abstraction, you would have to also include the `thread` and
`threads` cells.

```k
  rule <k> ++X => I +Int 1 ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> (I => I +Int 1) ...</store>  [group(increment)]
```

### Read
The `read()` construct evaluates to the first integer in the
input buffer, which it consumes. Note that this rule is put in the group
`increment`. This is because we will include it in the set of
potentially non-deterministic transitions when we kompile the definition;
we want to do that because two or more threads can "compete" on
reading the next integer from the input buffer, and different choices
for the next transition can lead to different behaviors.

```k
  rule <k> read() => I ...</k>
       <input> ListItem(I:Int) => .List ...</input>  [group(read)]
```

### Print
The `print` statement is strict, so all its arguments are
eventually evaluated (recall that `print` is variadic). We
append each of its evaluated arguments, in order, to the output buffer,
and structurally discard the residual `print` statement with an
empty list of arguments. We only want to allow printing integers and
strings, so we define a `Printable` syntactic category including
only these and define the `print` statement to only print
`Printable` elements. Alternatively, we could have had two
similar rules, one for integers and one for strings. Recall that,
currently, **K**'s lists are cons-lists, so we cannot simply rewrite the
head of a list (`P`) into a list (`.`). The first rule below is tagged,
because we want to include it in the list of transitions when we kompile;
different threads may compete on the output buffer and we want to capture
all behaviors.

```k
  syntax Printable ::= Int | String

/* currently it is necessary to subsort Printable to AExp,
  but future K should be able to infer that automatically. */
  syntax AExp ::= Printable

  context print(HOLE:AExp, _AEs:AExps);

  rule <k> print(P:Printable,AEs => AEs); ...</k>
       <output>... .List => ListItem(P) </output>  [group(print)]
  rule print(.AExps); => .
```

### Halt
The `halt` statement empties the computation, so the rewriting process
simply terminates as if the program terminated normally. Interestingly, once
we add threads to the language, the `halt` statement as defined below
will terminate the current thread only. If you want an abrupt termination
statement that halts the entire program, then you need to discard the entire
contents of the `threads` cell, so the entire computation abruptly
terminates the entire program, no matter how many concurrent threads it has,
because there is nothing else to rewrite.

```k
  rule <k> halt; ~> _ => . </k>
```

### Spawn thread
A spawned thread is passed its parent's environment at creation time.
The `spawn` expression in the parent thread is immediately
replaced by the unique identifier of the newly created thread, so the
parent thread can continue its execution. We only consider a sequentially
consistent shared memory model for IMP++, but other memory models can also
be defined in **K**; see, for example, the definition of KERNELC. Note that
the rule below does not need to be tagged in order to make it a transition
when we kompile, because the creation of the thread itself does not interfere
with the execution of other threads. Also, note that **K**'s configuration
abstraction is at heavy work here, in two different places. First, the
parent thread's `k` and `env` cells are wrapped within a
`thread` cell. Second, the child thread's `k`, `env`
and `id` cells are also wrapped within a `thread` cell. Why
that way and not putting all these four cells together within the
same thread, or even create an additional `threads` cell at top
holding a `thread` cell with the new `k`, `env`
and `id`? Because in the original configuration we declared
the multiplicity of the `thread` cell to be `*`, which
effectively tells the **K** tool that zero, one or more such cells can
co-exist in a configuration at any moment. The other cells have the
default multiplicity `one`, so they are not allowed to multiply.
Thus, the only way to complete the rule below in a way consistent with
the declared configuration is to wrap the first two cells in a
`thread` cell, and the latter two cells under the `.`
also in a `thread` cell. Once the rule applies, the spawning
thread cell will add a new thread cell next to it, which is consistent
with the declared configuration cell multiplicity. The unique identifier
of the new thread is generated using the `fresh` side condition.

```k
  rule <k> spawn S => !T:Int +Int 1 ...</k> <env> Rho </env>
       (.Bag => <thread>... <k> S </k> <env> Rho </env> <id> !T +Int 1 </id> ...</thread>)
```
### Join thread
A thread who wants to join another thread `T` has to wait until
the computation of `T` becomes empty. When that happens, the
join statement is simply dissolved. The terminated thread is not removed,
because we want to allow possible other join statements to also dissolve.

```k
  rule <k> join(T); => . ...</k> <thread>... <k>.</k> <id>T</id> ...</thread>
```

### Blocks
The body statement of a block is executed normally, making sure
that the environment at the block entry point is saved in the computation,
in order to be recovered after the block body statement. This step is
necessary because blocks can declare new variables having the same
name as variables which already exist in the environment, and our
semantics of variable declarations is to update the environment map in
the declared variable with a fresh location. Thus, variables which
are shadowed lose their original binding, which is why we take a
snapshot of the environment at block entrance and place it after the
block body (see the semantics of environment recovery at the end of
this module). Note that any store updates through variables which are
not declared locally are kept at the end of the block, since the store
is not saved/restored. An alternative to this environment save/restore
approach is to actually maintain a stack of environments and to push a
new layer at block entrance and pop it at block exit. The variable
lookup/assign/increment operations then also need to change, so we do
not prefer that non-modular approach. Compilers solve this problem by
statically renaming all local variables into fresh ones, to completely
eliminate shadowing and thus environment saving/restoring.

```k
  rule <k> {Ss} => Ss ~> Rho ...</k> <env> Rho </env>
```

### Variable declaration
We allocate a fresh location for each newly declared variable and
initialize it with 0.

```k
  rule <k> int (X,Xs => Xs); ...</k>
       <env> Rho => Rho[X <- !N:Int] </env>
       <store>... .Map => !N |-> 0 ...</store>
  rule int .Ids; => .
```

### Auxiliary operations
We only have one auxiliary operation in IMP++, the environment
recovery. Its role is to discard the current environment in the
`env` cell and replace it with the environment that it holds.

```k
  rule <k> Rho => . ...</k> <env> _ => Rho </env>
```

If you want to avoid useless environment recovery steps and keep the size
of the computation structure smaller, then you can also add the rule
```
  rule (_:Map => .) ~> _:Map
```
This rule acts like a ``tail recursion'' optimization, but for blocks. */
```k
// verification ids
  syntax Id ::= "n"     [token]
              | "sum"   [token]
              | "a"     [token]
              | "b"     [token]
              | "c"     [token]
endmodule
```
