K User Manual
=============

**NOTE:** The K User Manual is still **under construction**; some features of K
may have partial or missing documentation.

Introduction
------------

### Why K?

The K Framework is a programming language and system design toolkit made for
practioners and researchers alike.

**K For Practioners:**
*K is a framework for deriving programming languages tools from their semantic
specifications.*

Typically, programming language tool development follows a similar pattern.
After a new programming language is designed, separate teams will develop
separate language tools (e.g. a compiler, interpreter, parser, symbolic
execution engine, etc). Code reuse is uncommon. The end result is that for each
new language, the same basic tools and patterns are re-implemented again and
again.

K approaches the problem differently, by imagining how different tools could be
derived generically from a common specification. In other words, for any
language, a language-generic tool is a function that takes a language spec as
input and produces a tool as output. The end result is that the exercise of
designing new languages and their associated tooling is now reduced to
developing a single language specfication from which we derive our tooling *for
free*.

**K For Researchers:**
*K is a configuration- and rewrite-based executable semantic framework.*

In more detail, K specifications are:

1.   **Executable:** compile into runnable and testable programs;
2.   **Semantic:** correspond to a logical theory with a sound and relatively
     complete proof system;
3.   **Configuration-based:** organize system states into compositional,
     hierarchical, labelled units called cells;
4.   **Rewrite-based:** define system transitions using rewrite rules.

K specifications are compiled into particular *matching logic* theories, giving
them a simple and expressive semantics. K semantic rules are implicitly defined
over the entire configuration structure, but omit unused cells, enabling a
highly modular definitional style. Furthermore, K has been used to develop
programming languages, type systems, and formal analysis tools.

### Manual Objectives

As mentioned in the _Why K?_ section above, the K Framework is designed as a
collection of language-generic command-line interface (CLI) tools which revolve
around K specifications. These tools cover a broad range of uses, but they
typically fall into one of the following categories:

1.  Transforming K Specs (e.g. compilation)
2.  Running K Specs (e.g. concrete and symbolic execution)
3.  Analyzing K Specs (e.g. theorem proving)

The main *user-facing* K tools include:

-   `kompile` - the K compiler driver
-   `kparse` - the stanadlone K parser and abstract syntax tree (AST)
    transformation tool
-   `krun` - the K interpreter and symbolic execution engine driver
-   `kprove` - the K theorem prover

This user manual is designed to be a tool reference.
In particular, it is not desgined to be a tutorial on how to write K
specifications or to teach the logical foundations of K. New K users should
consult our dedicated
[K tutorial](https://kframework.org/k-distribution/k-tutorial/),
or the more language-design oriented
[PL tutorial](https://kframework.org/k-distribution/pl-tutorial/).
Researchers seeking to learn more about the logic underlying K are encouraged
to peruse the
[growing literature on K and matching logic](https://fsl.cs.illinois.edu/projects/pl/index.html).
We will consider the manual complete when it provides a complete description of
all user-facing K tools and features.

Introduction to K
-----------------

Since K specifications are the primary input into the entire system, let us
take a moment to describe them. At the highest level, K specifications describe
a programming language or system using three different pieces:

1.  the *system primitives*, the base datatypes used during system operation,
    e.g., numbers, lists, maps, etc;
2.  the *system state*, a tuple or record over system primitives which gives a
    complete snapshot of the system at any given moment;
3.  the *system behavior*, a set of rules which defines possible system
    evolutions.

K specifications are then defined by a collection of *sentences* which
correspond to the three concepts above:

1.  `syntax` declarations encode the *system primitives*;
2.  `configuration` declarations encode the *system state*;
3.  `context` and `rule` declarations encode the *system behavior*.

K sentences are then organized into one or *modules* which are stored in one or
more *files*. In this scheme, files may *require* other files and modules may
*import* other modules, giving rise to a hierarchy of files and modules. We
give an intuitive sketch of the two levels of grouping in the diagram below:

```
   example.k file
  +=======================+
  | requires ".." --------|--> File_1
  | ...                   |
  | requires ".." --------|--> File_N
  |                       |
  |  +-----------------+  |
  |  | module ..       |  |
  |  |   imports .. ---|--|--> Module_1
  |  |   ...           |  |
  |  |   imports .. ---|--|--> Module_M
  |  |                 |  |
  |  |   sentence_1    |  |
  |  |   ...           |  |
  |  |   sentence_K    |  |
  |  | endmodule       |  |
  |  +-----------------+  |
  |                       |
  +=======================+
```

where:

-   files and modules are denoted by double-bordered and single-borded boxes
    respectively;
-   file or module identifiers are denoted by double dots (`..`);
-   potential repititions are denoted by triple dots (`...`).

In the end, we require that the file and module hierarchies both form a
directed acyclic graph (DAG). This is, no file may recursively require itself,
and likewise, no module may recursively import itself.

We now zoom in further to discuss the various kinds of sentences contained in K
specifications:

1.  sentences that define our *system's primitives*, including:

    -   **sort declarations:** define new categories of primitive datatypes
    -   **Backus-Naur Form (BNF) grammar declarations:** define the
        operators that inhabit our primitive datatypes
    -   **lexical syntax declarations:** define lexemes/tokens for the
        lexer/tokenizer
    -   **syntax associativity declarations:** specify the
        associativity/grouping of our declared operators
    -   **syntax priority declarations:** specify the priority of
        potential ambiguous operators

2.  sentences that define our *system's state*, including:

    -   **configuration declarations:** define labelled, hierarchical records
        using an nested XML-like syntax

3.  sentences that define our *system's behavior*, including:

    -   **context declarations:** describe how primitives and configurations
        can simplify
    -   **context alias declarations:** define templates that can generate new
        contexts
    -   **rule declarations:** define how the system transitions from one state
        to the next

### K Process Overview

We now examine how the K tools are generally used. At a high-level, each K tool
can be understood as a blackbox with the following inputs and outputs:

```
 K Compilation Process
+============================================================+
|                     +---------+                            |
|  K Specification ---| kompile |--> Kore Specification --+  |
|                     +---------+                         |  |
+=========================================================|==+
                                                          |
 K Execution Process                                      |
+=========================================================|==+
|                                                         |  |
|             +-------------------------------------------+  |
|             |                                              |
|             |       +---------+                            |
|  K Term ----+-------| kparse  |--> K Term                  |
|             |       +---------+                            |
|             |                                              |
|             |       +---------+                            |
|  K Term ----+-------|  krun   |--> K Term                  |
|             |       +---------+                            |
|             |                                              |
|             |       +---------+                            |
|  K Claims --+-------| kprove  |--> K Claims                |
|                     +---------+                            |
|                                                            |
+============================================================+
```

where:

-   process outlines are denoted by boxes with double-lined borders
-   programs are denoted by boxes with single-lined borders
-   inputs and outputs are denoted by words attached to lines
-   K terms typically correspond to *programs* defined in a particular
    language's syntax (which are either parsed using `kparse` or executed using
    `krun`)
-   K claims are a notation for describing *how* certain K programs *should*
    execute (which are checked by our theorem prover `kprove`)

**K Compilation Process:**
Let us start with a description of the compilation process. According to the
above diagram, the compiler driver is called `kompile`. For our purposes, it is
enough to view the K compilation process as a black box that transforms a K
specification into a Kore specification file.

**K Execution Process:**
We now turn our attention to the K execution process. Abstractly, we can divide
the K execution process into the following stages:

1.  the kore specification is loaded (which defines a lexer, parser, and
    unparser among other things)
2.  the input string is lexed into a token stream
3.  the token stream is parsed into K terms/claims
4.  the K term/claims are transformed according the K tool being used (e.g.
    `kparse`, `krun`, or `kprove`)
5.  the K term/claims are unparsed into a string form and printed

Note that all of the above steps performed in K execution process are fully
prescribed by the input K specification. Of course, there are entire languages
devoted to encoding these various stages proces individually, e.g., `flex` for
lexers, `bison` for parsers, etc. What K offers is a _consistent_ language to
package the above concepts in a way that we believe is convenient and practical
for a wide range of uses.

Syntax Declaration
------------------

### Named Non-Terminals

We have added a syntax to Productions which allows non-terminals to be given a
name in productions. This significantly improves the ability to document K, by
providing a way to explicitly explain what a field in a production corresponds
to instead of having to infer it from a comment or from the rule body.

The syntax is:

```k
name: Sort
```

This syntax can be used anywhere in a K definition that expects a non-terminal.

### `klabel(_)` and `symbol` attributes

By default K generates for each syntax definition a long and obfuscated klabel
string, which serves as a unique internal identifier and also is used in kast
format of that syntax. If we need to reference a certain syntax production
externally, we have to manually define the klabels using the `klabel` attribute.
One example of where you would want to do this is to be able to refer to a given
symbol via the `syntax priorities` attribute, or to enable overloading of a
given symbol.

If you only provide the `klabel` attribute, you can use the provided `klabel` to
refer to that symbol anywhere in the frontend K code. However, the internal
identifier seen by the backend for that symbol will still be the long obfuscated
generated string. Sometimes you want control over the internal identfier used as
well, in which case you use the `symbol` attribute. This tells the frontend to
use whatever the declared `klabel` is directly as the internal identfier.

For example:

```k
module MYMODULE
    syntax FooBarBaz ::= #Foo( Int, Int ) [klabel(#Foo), symbol] // symbol1
                       | #Bar( Int, Int ) [klabel(#Bar)]         // symbol2
                       | #Baz( Int, Int )                        // symbol3
endmodule
```

Here, we have that:

-   In frontend K, you can refer to "symbol1" as `#Foo` (from `klabel(#Foo)`),
    and the backend will see `'Hash'Foo` as the symbol name.
-   In frontend K, you can refer to "symbol2" as `Bar` (from `klabel(#Bar)`),
    and the backend will see
    `'Hash'Bar'LParUndsCommUndsRParUnds'MYMODULE'Unds'FooBarBaz'Unds'Int'Unds'Int`
    as the symbol name.
-   In frontend K, you can refer to "symbol3" as
    `#Baz(_,_)_MYMODULE_FooBarBaz_Int_Int` (from auto-generated klabel), and
    the backend will see
    `'Hash'Baz'LParUndsCommUndsRParUnds'MYMODULE'Unds'FooBarBaz'Unds'Int'Unds'Int`
    as the symbol name.

The `symbol` provided *must* be unique to this definition. This is enforced by K.
In general, it's recommended to use `symbol` attribute whenever you use `klabel`
unless you explicitely have a reason not to (eg. you want to *overload* symbols,
or you're using a deprecated backend). It can be very helpful use the `symbol`
attribute for debugging, as many debugging messages are printed in Kast format
which will be more readable with the `symbol` names you explicitely declare.
In addition, if you are programatically manipulating definitions via the JSON
Kast format, building terms using the user-provided pretty
`symbol, klabel(...)` is easier and less error-prone when the auto-generation
process for klabels changes.

### Parametric productions and `bracket` attributes

Some syntax productions, like the rewrite operator, the bracket operator, and
the #if #then #else #fi operator, cannot have their precise type system
expressed using only concrete sorts.

Prior versions of K solved this issue by using the K sort in this case, but
this introduces inexactness in which poorly typed terms can be created even
without having a cast operator present in the syntax, which is a design
consideration we would prefer to avoid.

It also introduces cases where terms cannot be placed in positions where they
ought to be well sorted unless their return sort is made to be KBott, which in
turn vastly complicates the grammar and makes parsing much slower.

In order to introduce this, we provide a new syntax for parametric productions
in K. This allows you to express syntax that has a sort signature based on
parametric polymorphism. We do this by means of an optional curly-brace-
enclosed list of parameters prior to the return sort of a production.

Some examples:

```k
syntax {Sort} Sort ::= "(" Sort ")" [bracket]
syntax {Sort} KItem ::= Sort
syntax {Sort} Sort ::= KBott
syntax {Sort} Sort ::= Sort "=>" Sort
syntax {Sort} Sort ::= "#if" Bool "#then" Sort "#else" Sort "#fi"
syntax {Sort1, Sort2} Sort1 ::= "#fun" "(" Sort2 "=>" Sort1 ")" "(" Sort2 ")"
```

Here we have:

1. Brackets, which can enclose any sort but should be of the same sort that was
   enclosed
2. Every sort is a KItem.
3. A KBott term can appear inside any sort
4. Rewrites, which can rewrite a value of any sort to a value of the same sort,
   or to a different sort which is allowed in that context
5. If then else, which can return any sort but which must contain that sort on
   both the true and false branches.
6. lambda applications, in which the argument and parameter must be the same
   sort, and the return value of the application must be the same sort as the
   return value of the function.

Note the last case, in which two different parameters are specified separated
by a comma. This indicates that we have multiple independent parameters which
must be the same each place they occur, but not the same as the other
parameters.

In practice, because every sort is a subsort of K, the `Sort2`
parameter in #6 above does nothing during parsing. It cannot
actually reject any parse, because it can always infer that the sort of the
argument and parameter are K, and it has no effect on the resulting sort of
the term. However, it will nevertheless affect the kore generated from the term
by introducing an additional parameter to the symbol generated for the term.

### `function` and `functional` attributes

Many times it becomes easier to write a semantics if you have "helper"
functions written which can be used in the RHS of rules. The `function`
attribute tells K that a given symbol should be simplified immediately when it
appears anywhere in the configuration. Semantically, it means that evaluation
of that symbol will result in at most one return value (that is, the symbol is
a *partial function*).

The `functional` attribute indicates to the symbolic reasoning engine that a
given symbol is a *total function*, that is it has *exactly* one return value
for every possible input.

For example, here we define the `_+Word_` total function and the `_/Word_`
partial function, which can be used to do addition/division modulo
`2 ^Int 256`. These functions can be used anywhere in the semantics where
integers should not grow larger than `2 ^Int 256`. Notice how `_/Word_` is
*not* defined when the denominator is `0`.

```k
syntax Int ::= Int "+Word" Int [function, functional]
             | Int "/Word" Int [function]

rule I1 +Word I2 => (I1 +Int I2) modInt (2 ^Int 256)
rule I1 /Word I2 => (I1 /Int I2) modInt (2 ^Int 256) requires I2 =/=Int 0
```

### `freshGenerator` attribute

In K, you can access "fresh" values in a given domain using the syntax
`!VARNAME:VarSort` (with the `!`-prefixed variable name). This is supported for
builtin sorts `Int` and `Id` already. For example, you can generate fresh
memory locations for declared identifiers as such:

```k
rule <k> new var x ; => . ... </k>
     <env> ENV => ENV [ x <- !I:Int ] </env>
     <mem> MEM => MEM [ !I <- 0     ] </mem>
```

Each time a `!`-prefixed variable is encountered, a new integer will be used,
so each variable declared with `new var _ ;` will get a unique position in the
`<mem>`.

Sometimes you want to have generation of fresh constants in a user-defined
sort. For this, K will still generate a fresh `Int`, but can use a converter
function you supply to turn it into the correct sort. For example, here we can
generate fresh `Foo`s using the `freshFoo(_)` function annotated with
`freshGenerator`.

```k
syntax Foo ::= "a" | "b" | "c" | d ( Int )

syntax Foo ::= freshFoo ( Int ) [freshGenerator, function, functional]

rule freshFoo(0) => a
rule freshFoo(1) => b
rule freshFoo(2) => c
rule freshFoo(I) => d(I) [owise]

rule <k> new var x ; => . ... </k>
     <env> ENV => ENV [ x <- !I:Int  ] </env>
     <mem> MEM => MEM [ !I <- !F:Foo ] </mem>
```

Now each newly allocated memory slot will have a fresh `Foo` placed in it.

### `token` attribute

The `token` attribute signals to the Kore generator that the associated sort
will be inhabited by domain values. Sorts inhabited by domain values must not
have any constructors declared.

```k
syntax Bytes [hook(BYTES.Bytes), token]
```

### Converting between `[token]` sorts

You can convert between tokens of one sort via `String`s by defining functions
implemented by builtin hooks.
The hook `STRING.token2string` allows conversion of any token to a string:

```k
syntax String ::= FooToString(Foo)  [function, functional, hook(STRING.token2string)]
```

Similarly, the hook `STRING.string2Token` allows the inverse:

```k
syntax Bar ::= StringToBar(String) [function, functional, hook(STRING.string2token)]
```

WARNING: This sort of conversion does *NOT* do any sort of parsing or validation.
Thus, we can create arbitary tokens of any sort:

```
StringToBar("The sun rises in the west.")
```

Composing these two functions lets us convert from `Foo` to `Bar`

```k
syntax Bar ::= FooToBar(Foo) [function]
rule FooToBar(F) => StringToBar(FooToString(F))
```

### Parsing comments, and the `#Layout` sort

Productions for the `#Layout` sort are used to describe tokens that are
considered "whitespace". The scanner removes tokens matching these productions
so they are not even seen by the parser. Below, we use it to define
lines begining with `;` (semicolon) as comments.

```k
syntax #Layout ::= r"(;[^\\n\\r]*)"    // Semi-colon comments
                 | r"([\\ \\n\\r\\t])" // Whitespace
```

### `prec` attribute

Consider the following naive attempt at creating a language what syntax that
allows two types of variables: names that contain underbars, and names that
contain sharps/hashes/pound-signs:

```k
syntax NameWithUnderbar ::= r"[a-zA-Z][A-Za-z0-9_]*"  [token]
syntax NameWithSharp    ::= r"[a-zA-Z][A-Za-z0-9_#]*" [token]
syntax Pgm ::= underbar(NameWithUnderbar)
             | sharp(NameWithSharp)
```

Although, it seems that K has enough information to parse the programs
`underbar(foo)` and `sharp(foo)` with, the lexer does not take into account
whether a token is being parsed for the `sharp` or for the `underbar`
production. It chooses an arbitary sort for the token `foo` (perhaps
`NameWithUnderbar`). Thus, during paring it is unable to construct a valid term
for one of those programs (`sharp(foo)`) and produces the error message:
`Inner Parser: Parse error: unexpected token 'foo'.`

Since calculating inclusions and intersections between regular expressions is
tricky, we must provide this information to K. We do this via the `prec(N)`
attribute. The lexer will always prefer longer tokens to shorter tokens.
However, when it has to choose between two different tokens of equal length,
token productions with higher precedence are tried first. Note that the default
precedence value is zero when the `prec` attribute is not specified.

We also need to make sorts with more specific tokens subsorts of ones with more
general tokens. We add the token attribute to this production so that all
tokens of a particular sort are marked with the sort it is parsed as, and not a
subsort thereof. e.g. we get `underbar(#token("foo", "NameWithUnderbar"))`
instead of `underbar(#token("foo", "#LowerId"))`

The `BUILTIN-ID-TOKENS` module defines `#UpperId` and `#LowerId` with
attributes `prec(2)`.

```k
imports BUILTIN-ID-TOKENS
syntax NameWithUnderbar ::= r"[a-zA-Z][A-Za-z0-9_]*" [prec(1), token]
                          | #UpperId                [token]
                          | #LowerId                [token]
syntax NameWithSharp ::= r"[a-zA-Z][A-Za-z0-9_#]*" [prec(1), token]
                       | #UpperId                 [token]
                       | #LowerId                 [token]
syntax Pgm ::= underbar(NameWithUnderbar)
             | sharp(NameWithSharp)
```

### `unused` attribute

K will warn you if you declare a symbol that is not used in any of the rules of
your definition. Sometimes this is intentional, however; in this case, you can
suppress the warning by adding the `unused` attribute to the production or
cell.

```k
syntax Foo ::= foo() [unused]

configuration <foo unused=""> .K </foo>
```

### Symbol priority and associativity

Unlike most other parser generators, K combines the task of parsing with AST
generation. A production declared with the `syntax` keyword in K is both a
piece of syntax used when parsing, and a symbol that is used when rewriting.
As a result, it is generally convenient to describe expression grammars using
priority and associativity declarations rather than explicitly transforming
your grammar into a series of nonterminals, one for each level of operator
precedence. Thus, for example, a simple grammar for addition and multiplication
will look like this:

```k
syntax Exp ::= Exp "*" Exp
             | Exp "+" Exp
```

However, this grammar is ambiguous. The term `x+y*z` might refer to `x+(y*z)`
or to `(x+y)*z`. In order to differentiate this, we introduce a partial
ordering between productions known as priority. A symbol "has tighter priority"
than another symbol if the first symbol can appear under the second, but the
second cannot appear under the first without a bracket. For example, in
traditional arithmetic, multiplication has tighter priority than addition,
which means that `x+y*z` cannot parse as `(x+y)*z` because the addition
operator would appear directly beneath the multiplication, which is forbidden
by the priority filter.

Priority is applied individually to each possible ambiguous parse of a term. It
then either accepts or rejects that parse. If there is only a single remaining
parse (after all the other disambiguation steps have happened), this is the
parse that is chosen. If all the parses were rejected, it is a parse error. If
multiple parses remain, they might be resolved by further disambiguation such
as via the `prefer` and `avoid` attributes, but if multiple parses remain after
disambiguation finishes, this is an ambiguous parse error, indicating there is
not a unique parse for that term. In the vast majority of cases, this is
an error and indicates that you ought to either change your grammar or add
brackets to the term in question.

Priority is specified in K grammars by means of one of two different
mechanisms. The first, and simplest, simply replaces the `|` operator in a
sequence of K productions with the `>` operator. This operator indicates that
everything prior to the `>` operator (including transitively) binds tighter
than what comes after. For example, a more complete grammar for simple
arithmetic might be:

```k
syntax Exp ::= Exp "*" Exp
             | Exp "/" Exp
             > Exp "+" Exp
             | Exp "-" Exp
```

This indicates that multiplication and division bind tigher than addition
and subtraction, but that there is no relationship in priority between
multiplication and division.

As you may have noticed, this grammar is also ambiguous. `x*y/z` might refer to
`x*(y/z)` or to `(x*y)/z`. Indeed, if we removed division and subtraction
entirely, the grammar would still be ambiguous: `x*y*z` might parse as
`x*(y*z)`, or as `(x*y)*z`. To resolve this, we introduce another feature:
associativity. Roughly, asssociativity tells us how symbols are allowed to nest
within other symbols with the same priority. If a set of symbols is left
associative, then symbols in that set cannot appear as the rightmost child
of other symbols in that set. If a set of symbols is right associative, then
symbols in that set cannot appear as the leftmost child of other symbols in
that set. Finally, if a set of symbols is non-associative, then symbols
in that set cannot appear as the rightmost or leftmost child of other symbols
in that set. For example, in the above example, if addition and subtraction
are left associative, then `x+y+z` will parse as `(x+y)+`z and `x+y-z` will
parse as `(x+y)-z` (because the other parse will have been rejected).

You might notice that this seems to apply only to binary infix operators. In
fact, the real behavior is slightly more complicated. Priority and
associativity (for technical reasons that go beyond the scope of this document)
really only apply when the rightmost or leftmost item in a production is a
nonterminal. If the rightmost nonterminal is followed by a terminal (or
respectively the leftmost preceded), priority and associativity do not apply.
Thus we can generalize these concepts to arbitrary context-free grammars.

Note that in some cases, this is not the behavior you want. You may actually
want to reject parses even though the leftmost and rightmost item in a
production are terminals. You can accomplish this by means of the
`applyPriority` attribute. When placed on a production, it tells the parser
which nonterminals of a production the priority filter ought to reject children
under, overriding the default behavior. For example, I might have a production
like `syntax Exp ::= foo(Exp, Exp) [applyPriority(1)]`. This tells the parser
to reject terms with looser priority binding under the first `Exp`, but not
the second. By default, with this production, neither position would apply
to the priority filter, because the first and last items of the production
are both terminals.

Associativity is specified in K grammars by means of one of two different
mechanisms. The first, and simplest, adds the associativity of a priority block
of symbols prior to that block. For example, we can remove the remaining
ambiguities in the above grammar like so:

```k
syntax Exp ::= left:
               Exp "*" Exp
             | Exp "/" Exp
             > right:
               Exp "+" Exp
             | Exp "-" Exp
```

This indicates that multiplication and division are left-associative, ie, after
symbols with higher priority are parsed as innermost, symbols are nested with
the rightmost on top. Addition and subtraction are right associative, which
is the opposite and indicates that symbols are nested with the leftmost on top.
Note that this is similar but different from evaluation order, which also
concerns itself with the ordering of symbols, which is described in the next
section.

You may note we have not yet introduced the second syntax for priority
and associativity. In some cases, syntax for a grammar might be spread across
multiple modules, sometimes for very good reasons with respect to code
modularity. As a result, it becomes infeasible to declare priority and
associativity inline within a set of productions, because the productions
are not contiguous within a single file.

For this purpose, we introduce the equivalent `syntax priorities`,
`syntax left`, `syntax right`, and `syntax non-assoc` declarations. For
example, the above grammar can be written equivalently as:

```k
syntax Exp ::= Exp "*" Exp [mult]
             | Exp "/" Exp [div]
             | Exp "+" Exp [add]
             | Exp "-" Exp [sub]

syntax priorities mult div > add sub
syntax left mult div
syntax right add sub
```

Here we use user-defined attributes to refer to a group of sentences
collectively. The sets are flattened together. We could equivalently have
written:

```k
syntax Exp ::= Exp "*" Exp [mult]
             | Exp "/" Exp [mult]
             | Exp "+" Exp [add]
             | Exp "-" Exp [add]

syntax priorities mult > add
syntax left mult
syntax right add
```

Note that there is one other way to describe associativity, but it is
prone to a very common mistake. You can apply the attribute `left`, `right`,
or `non-assoc` directly to a production to indicate that it is, by itself,
left-, right-, or non-associative.

However, this often does not mean what users think it means. In particular:

```k
syntax Exp ::= Exp "+" Exp [left]
             | Exp "-" Exp [left]
```

is not equivalent to:

```k
syntax Exp ::= left:
               Exp "+" Exp
             | Exp "-" Exp
```

Under the first, each production is associative with itself, but not each
other. Thus, `x+y+z` will parse unambiguously as `(x+y)+z`, but `x+y-z` will
be ambiguous. However, in the second, `x+y-z` will parse unambiguously as
`(x+y)-z`.

Think carefully about how you want your grammar to parse. In general, if you're
not sure, it's probably best to group associativity together into the same
blocks you use for priority, rather than using `left`, `right`, or `non-assoc`
attributes on the productions.

### Lexical identifiers

Sometimes it is convenient to be able to give a certain regular expression a
name and then refer to it in one or more regular expression terminals. This
can be done with a `syntax lexical` sentence in K:

```k
syntax lexical Alphanum = r"[0-9a-zA-Z]"
```

This defines a lexical identifier `Alphanum` which can be expanded in any
regular expression terminal to the above regular expression. For  example, I
might choose to then implement the syntax of identifiers as follows:

```k
syntax Id ::= r"[a-zA-Z]{Alphanum}*" [token]
```

Here `{Alphanum}` expands to the above regular expression, making the sentence
equivalent to the following:

```k
syntax Id ::= r"[a-zA-Z]([0-9a-zA-Z])*" [token]
```

This feature can be used to more modularly construct the lexical syntax of your
language. Note that K does not currently check that lexical identifiers used
in regular expressions have been defined; this will generate an error when
creating the scanner, however, and the user ought to be able to debug what
happened.

### `assoc`, `comm`, `idem`, and `unit` attributes

These attributes are used to indicate whether a collection or a production
is associative, commutative, idempotent, and/or has a unit.
In general, you should not need to apply these attributes to productions
yourself, however, they do have certain special meaning to K. K will generate
axioms related to each of these concepts into your definition for you
automatically. It will also automatically sort associative-commutative
collections, and flatten the indentation of associative collections, when
unparsing.


Configuration Declaration
-------------------------

### `exit` attribute

A single configuration cell containing an integer may have the "exit"
attribute. This integer will then be used as the return value on the console
when executing the program.

For example:

```k
configuration <k> $PGM:Pgm </k>
              <status-code exit=""> 1 </status-code>
```

declares that the cell `status-code` should be used as the exit-code for
invocations of `krun`. Additionally, we state that the default exit-code is `1`
(an error state). One use of this is for writing testing harnesses which assume
that the test fails until proven otherwise and only set the `<status-code>` cell
to `0` if the test succeeds.

### Collection Cells: `multiplicity` and `type` attributes

Sometimes a semantics needs to allow multiple copies of the same cell, for
example if you are making a concurrent multi-threading programming language.
For this purpose, K supports the `multiplicity` and `type` attributes on cells
declared in the configuration.

`multiplicity` can take on values `*` and `?`. Declaring `multiplicity="*"`
indicates that the cell may appear any number of times in a runtime
configuration. Setting `multiplicity="?"` indicates that the cell may only
appear exactly 0 or 1 times in a runtime configuration. If there are no
configuration variables present in the cell collection, the initial
configuration will start with exactly 0 instances of the cell collection. If
there are configuration variables present in the cell collection, the initial
configuration will start with exactly 1 instance of the cell collection.

`type` can take on values `Set`, `List`, and `Map`. For example, here we declare
several collecion cells:

```k
configuration <k> $PGM:Pgm </k>
              <sets>  <set  multiplicity="?" type="Set">  0:Int </set>  </sets>
              <lists> <list multiplicity="*" type="List"> 0:Int </list> </lists>
              <maps>
                <map multiplicity="*" type="Map">
                  <map-key> 0:Int </map-key>
                  <map-value-1> "":String </map-value-1>
                  <map-value-2> 0:Int     </map-value-2>
                </map>
              </maps>
```

Declaring `type="Set"` indicates that duplicate occurrences of the cell should
be de-duplicated, and accesses to instances of the cell will be nondeterministic
choices (constrained by any other parts of the match and side-conditions).
Similarly, declaring `type="List"` means that new instances of the cell can be
added at the front or back, and elements can be accessed from the front or back,
and the order of the cells will be maintained. The following are examples of
introduction and elimination rules for these collections:

```k
rule <k> introduce-set(I:Int) => . ... </k>
     <sets> .Bag => <set> I </set> </sets>

rule <k> eliminate-set => I ... </k>
     <sets> <set> I </set> => .Bag </sets>

rule <k> introduce-list-start(I:Int) => . ... </k>
     <lists> (.Bag => <list> I </list>) ... </lists>

rule <k> introduce-list-end(I:Int) => . ... </k>
     <lists> ... (.Bag => <list> I </list>) </lists>

rule <k> eliminate-list-start => I ... </k>
     <lists> (<list> I </list> => .Bag) ... </lists>

rule <k> eliminate-list-end => I ... </k>
     <lists> ... (<list> I </list> => .Bag) </lists>
```

Notice that for `multiplicity="?"`, we only admit a single `<set>` instance at
a time. For the `type=List` cell, we can add/eliminate cells from the from or
back of the `<lists>` cell. Also note that we use `.Bag` to indicate the empty
cell collection in all cases.

Declaring `type="Map"` indicates that the first sub-cell will be used as a
cell-key. This means that matching on those cells will be done as a map-lookup
operation if the cell-key is mentioned in the rule (for performance). If the
cell-key is not mentioned, it will fallback to normal nondeterministic
constrained by other parts of the match and any side-conditions. Note that there
is no special meaning to the name of the cells (in this case `<map>`,
`<map-key>`, `<map-value-1>`, and `<map-value-2>`). Additionally, any number of
sub-cells are allowed, and the _entire_ instance of the cell collection is
considered part of the cell-value, including the cell-key (`<map-key>` in this
case) and the surrounding collection cell (`<map>` in this case).

For example, the following rules introduce, set, retrieve from, and eliminate
`type="Map"` cells:

```k
rule <k> introduce-map(I:Int) => . ... </k>
     <maps> ... (.Bag => <map> <map-key> I </map-key> ... </map>) ... </maps>

rule <k> set-map-value-1(I:Int, S:String) => . ... </k>
     <map> <map-key> I </map-key> <map-value-1> _ => S </map-value-1> ... </map>

rule <k> set-map-value-2(I:Int, V:Int) => . ... </k>
     <map> <map-key> I </map-key> <map-value-2> _ => V </map-value-2> ... </map>

rule <k> retrieve-map-value-1(I:Int) => S ... </k>
     <map> <map-key> I </map-key> <map-value-1> S </map-value-1> ... </map>

rule <k> retrieve-map-value-2(I:Int) => V ... </k>
     <map> <map-key> I </map-key> <map-value-2> V </map-value-2> ... </map>

rule <k> eliminate-map(I:Int) => . ... </k>
     <maps> ... (<map> <map-key> I </map-key> ... </map> => .Bag) ... </maps>
```

Note how each rule makes sure that `<map-key>` cell is mentioned, and we
continue to use `.Bag` to indicate the empty collection. Also note that
when introducing new map elements, you may omit any of the sub-cells which are
not the cell-key. In case you do omit sub-cells, you must use structural
framing `...` to indicate the missing cells, they will receive the default
value given in the `configuration ...` declaration.


Rule Declaration
----------------

### Pattern Matching operator

Sometimes when you want to express a side condition, you want to say that a
rule matches if a particular term matches a particular pattern, or if it
instead does /not/ match a particular pattern.

The syntax in K for this is :=K and :/=K. It has similar meaning to ==K and
=/=K, except that where ==K and =/=K express equality, :=K and =/=K express
model membership. That is to say, whether or not the rhs is a member of the set
of terms expressed by the lhs pattern. Because the lhs of these operators is a
pattern, the user can use variables in the lhs of the operator. However, due to
current limitations, these variables are *NOT* bound in the rest of the term.
The user is thus encouraged to use anonymous variables only, although this is
not required.

This is compiled by the K frontend down to an efficient pattern matching on a
fresh function symbol.

### Anonymous function applications

There are a number of cases in K where you would prefer to be able to take some
term on the RHS, bind it to a variable, and refer to it in multiple different
places in a rule.

You might also prefer to take a variable for which you know some of its
structure, and modify some of its internal structure without requiring you to
match on every single field contained inside that structure.

In order to do this, we introduce syntax to K that allows you to construct
anonymous functions in the RHS of a rule and apply them to a term.

The syntax for this is:

```
#fun(RuleBody)(Argument)
```

Note the limitations currently imposed by the implementation. These functions
are not first-order: you cannot bind them to a variable and inject them like
you can with a regular klabel for a function. You also cannot express multiple
rules or multiple parameters, or side conditions. All of these are extensions
we would like to support in the future, however.

In the following, we use three examples to illustrate the behavior of `#fun`.
We point out that the support for `#fun` is provided by the frontend, not the
backends.

The three examples are real examples borrowed or modified from existing language
semantics.

*Example 1 (A Simple Self-Explained Example).*

```
#fun(V:Val => isFoo(V) andBool isBar(V))(someFunctionReturningVal())
```

*Example 2 (Nested #fun).*

```
   #fun(C
=> #fun(R
=> #fun(E
=> foo1(E, R, C)
  )(foo2(C))
  )(foo3(0))
  )(foo4(1))
```

This example is from the `beacon`
semantics:https://github.com/runtimeverification/beacon-chain-spec/blob/master/b
eacon-chain.k at line 302, with some modification for simplicity. Note how
variables `C, R, E` are bound in the nested `#fun`.

*Example 3 (Matching a structure).*

```
rule foo(K, RECORD) =>
  #fun(record(... field: _ => K))(RECORD)
```

Unlike previous examples, the LHS of `#fun` in this example is no longer a
variable, but a structure. It has the same spirit as the first two examples,
but we match the `RECORD` with a structure `record( DotVar, field: X)`, instead
of a standalone variable. We also use K's local rewrite syntax (i.e., the
rewriting symbol `=>` does not occur at the top-level) to prevent writing
duplicate expressions on the LHS and RHS of the rewriting.


### Macros and Aliases

A rule can be tagged with the `macro`, `alias`, `macro-rec`, or `alias-rec`
attributes. In all cases, what this signifies is that this is a macro rule.
Macro rules are applied statically during compilation on all terms that they
match, and statically before program execution on the initial configuration.
Currently, macros are required to not have side conditions, although they can
contain sort checks.

When a rule is tagged with the `alias` attribute, it is also applied statically
in reverse prior to unparsing on the final configuration. Note that a macro can
have unbound variables in the right hand side. When such a macro exists, it
should be used only on the left hand side of rules, unless the user is
performing symbolic execution and expects to introduce symbolic terms into the
subject being rewritten.

However, when used on the left hand side of a rule, it functions similarly to a
pattern alias, and allows the user to concisely express a reusable pattern that
they wish to match on in multiple places.

For example, consider the following semantics:

```k
syntax KItem ::= "foo" | "foobar"
syntax KItem ::= bar(KItem) | baz(Int, KItem)
rule foo => foobar [alias]
rule bar(I) => baz(?_, I) [macro]
rule bar(I) => I
```

This will rewrite `baz(0, foo)` to `foo`. First `baz(0, foo)` will be rewritten
statically to `baz(0, foobar)`. Then the non-`macro` rule will apply (because
the rule will have been rewritten to `rule baz(_, I) => I`). Then `foobar` will
be rewritten statically after rewriting finishes to `foo` via the reverse form
of the alias.

Note that macros do not apply recursively within their own expansion. This is
done so as to ensure that macro expansion will always terminate. If the user
genuinely desires a recursive macro, the `macro-rec` and `alias-rec` attributes
can be used to provide this behavior.

For example, consider the following semantics:

```k
syntax Exp ::= "int" Exps ";" | Exp Exp | Id
syntax Exps ::= List{Exp,","}

rule int X:Id, X':Id, Xs:Exps ; => int X ; int X', Xs ; [macro]
```

This will expand `int x, y, z;` to `int x; int y, z;` because the macro does
not apply the second time after applying the substitution of the first
application. However, if the `macro` attribute were changed to the `macro-rec`
attribute, it would instead expand (as the user likely intended) to
`int x; int y; int z;`.

The `alias-rec` attribute behaves with respect to the `alias` attribute the
same way the `macro-rec` attribute behaves with respect to `macro`.

### `anywhere` rules

Some rules are not functional, but you want them to apply anywhere in the
configuration (similar to functional rules). You can use the `anywhere`
attribute on a rule to instruct the backends to make sure they apply anywhere
they match in the entire configuration.

For example, if you want to make sure that some associative operator is always
right-associated anywhere in the configuration, you can do:

```k
syntax Stmt ::= Stmt ";" Stmt

rule (S1 ; S2) ; S3 => S1 ; (S2 ; S3) [anywhere]
```

Then after every step, all occurances of `_;_` will be re-associated. Note that
this allows the symbol `_;_` to still be a constructor, even though it is
simplified similarly to a `function`.

### `smt-lemma`, `lemma`, and `trusted` attributes

These attributes guide the prover when it tries to apply rules to discharge a
proof obligation.

-   `smt-lemma` can be applied to a rule to encode it as an equality when
    sending queries to Z3.
-   `lemma` distinguishes normal rules from lemma rules in the semantics, but
    has no affect.
-   `trusted` instructs the prover that it should not attempt proving a given
    proof obligation, instead trusting that it is true.

### Projection and Predicate functions

K automatically generates certain predicate and projection functions from the
syntax you declare. For example, if you write:

```k
syntax Foo ::= foo(bar: Bar)
```

It will automatically generate the following K code:

```k
syntax Bool ::= isFoo(K) [function]
syntax Foo ::= "{" K "}" ":>Foo" [function]
syntax Bar ::= bar(Foo) [function]

rule isFoo(F:Foo) => true
rule isFoo(_) => false [owise]

rule { F:Foo }:>Foo => F
rule bar(foo(B:Bar)) => B
```

The first two types of functions are generated automatically for every sort in
your K definition, and the third type of function is generated automatically
for each named nonterminal in your definition. Essentially, `isFoo` for some
sort `Foo` will tell you whether a particular term of sort `K` is a `Foo`,
`{F}:>Foo` will cast `F` to sort `Foo` if `F` is of sort `Foo` and will be
undefined (i.e., theoretically defined as `#Bottom`, the bottom symbol in
matching logic) otherwise. Finally, `bar` will project out the child of a `foo`
named `bar` in its production declaration.

Note that if another term of equal or smaller sort to `Foo` exists and has a
child named `bar` of equal or smaller sort to `Bar`, this will generate an
ambiguity during parsing, so care should be taken to ensure that named
nonterminals are sufficiently unique from one another to prevent such
ambiguities. Of course, the compiler will generate a warning in this case.

### `simplification` attribute (Haskell backend)

The simplification attribute identifies rules outside the main semantics that
are used to simplify function patterns.

**Conditions**: A simplification rule is applied by _matching_ the function
arguments, instead of unification as when applying function definition
rules. This allows function symbols to appear nested as arguments to other
functions on the left-hand side of a simplification rule, which is forbidden in
function definition rules. For example, this rule would not be accepted as a
function definition rule:

```k
rule (X +Int Y) +Int Z => X +Int (Y +Int Z) [simplification]
```

A simplification rule is only applied when the current side condition _implies_
the `requires` clause of the rule, like function definition rules.

**Order**: Simplification rules are applied after definition rules, if no
definition rule did apply. The `simplification` attribute accepts an optional
integer argument which is the rule's _priority_; if the optional argument is not
specified, it is equivalent to a priority of 50. Simplification rules are
applied in order of their priority. `simplification` rules may not have the
`priority` attribute.

For example, for the following definition:

```k
    syntax WordStack ::= Int ":" WordStack | ".WordStack"
    syntax Int ::= sizeWordStack    ( WordStack       ) [function]
                 | sizeWordStackAux ( WordStack , Int ) [function]
 // --------------------------------------------------------------
    rule sizeWordStack(WS) => sizeWordStackAux(WS, 0)

    rule sizeWordStackAux(.WordStack, N) => N
    rule sizeWordStackAux(W : WS    , N) => sizeWordStackAux(WS, N +Int 1)
```

We might add the following simplification lemma:

```k
    rule sizeWordStackAux(WS, N) => N +Int sizeWordStackAux(WS, 0)
      requires N =/=Int 0
      [simplification]
```

Then this simplification rule will only apply if the Haskell backend can prove
that `notBool N =/=Int 0` is unsatisfiable. This avoids an infinite cycle of
applying this simplification lemma.

**NOTE**: The frontend and Haskell backend **do not check** that supplied
simplification rules are sound, this is the developer's responsibility. In
particular, rules with the simplification attribute must preserve definedness;
that is, if the left-hand side refers to any partial function then:

-   the right-hand side must be `#Bottom` when the left-hand side is `#Bottom`, or
-   the rule must have an `ensures` clause that is `false` when the left-hand
    side is `#Bottom`, or
-   the rule must have a `requires` clause that is `false` when the left-hand
    side is `#Bottom`.

These conditions are in order of decreasing preference: the best option is to
preserve `#Bottom` on the right-hand side, the next best option is to have an
`ensures` clause, and the least-preferred option is to have a `requires` clause.
The most preferred option is to write total functions and avoid the entire issue.

### `concrete` attribute, `#isConcrete` and `#isVariable` function (Java backend)

**NOTE**: The Haskell backend _does not_ and _will not_ support the
meta-functions `#isConcrete` and `#isVariable`. See below for information about
the `concrete` and `symbolic` attributes in the Haskell backend.

Sometimes you only want a given function to simplify if all (or some) of the
arguments are concrete (non-symbolic). To do so, you can use either the
`concrete` attribute (if you want it to only apply when all arguments are
concrete), or the `#isConcrete(_)` side-condition (when you only want it to
apply if some arguments are concrete). Conversly, the function `#isVariable(_)`
will only return true when the argument is a variable.

For example, the following will only re-associate terms when all arguments
are concrete:

```k
rule X +Int (Y +Int Z) => (X +Int Y) +Int Z [concrete]
```

And the following rules will only re-associate terms when it will end up
grouping concrete sub-terms:

```k
rule X +Int (Y +Int Z) => (X +Int Y) +Int Z
  requires #isConcrete(X)
   andBool #isConcrete(Y)
   andBool #isVariable(Z)

rule X +Int (Y +Int Z) => (X +Int Z) +Int Y
  requires #isConcrete(X)
   andBool #isConcrete(Z)
   andBool #isVariable(Y)
```

### `concrete` and `symbolic` attributes (Haskell backend)

Sometimes you only want a rule to apply if some or all arguments are concrete
(not symbolic). This is done with the `concrete` attribute. Conversely, the
`symbolic` attribute will allow a rule to apply only when some arguments are not
concrete. These attributes should only be given with the `simplification`
attribute.

For example, the following will only re-associate terms when all arguments
are concrete:

```k
rule X +Int (Y +Int Z) => (X +Int Y) +Int Z [simplification, concrete]
```

These rules will re-associate and commute terms to combine concrete arguments:

```k
rule (A +Int Y) +Int Z => A +Int (Y +Int Z)
  [concrete(Y, Z), symbolic(A), simplification]

rule X +Int (B +Int Z) => B +Int (X +Int Z)
  [concrete(X, Z), symbolic(B), simplification]
```

### The `unboundVariables` attribute

Normally, K rules are not allowed to contain regular (i.e., not fresh, not
existential) variables in the RHS / `requires` / `ensures` clauses which are not
bound in the LHS.

However, in certain cases this behavior might be desired, like, for example,
when specifying a macro rule which is to be used in the LHS of other rules.
To allow for such cases, but still be useful and perform the unboundness checks
in regular cases, the `unboundVariables` attributes allows the user to specify
a comma-separated list of names of variables which can be unbound in the rule.

For example, in the macro declaration
```k
  rule cppEnumType => bar(_, scopedEnum() #Or unscopedEnum() ) [macro, unboundVariables(_)]
```
the declaration `unboundVariables(_)` allows the rule to pass the unbound
variable checks, and this in turn allows for `cppEnumType` to be used in
the LHS of a rule to mean the pattern above:
```k
  rule inverseConvertType(cppEnumType, foo((cppEnumType #as T::CPPType => underlyingType(T))))
```

### The `memo` attribute

The `memo` attribute is a hint from the user to the backend to memoize a
function. Not all backends support memoization, but when the attribute is used
and the definition is compiled for a `memo`-supporting backend, then calls to
the function may be cached. At the time of writing, the Haskell and OCaml
backends support memoization.

#### Limitations of memoization with the Haskell backend

The Haskell backend will only cache a function call if all arguments are concrete.

It is recommended not to memoize recursive functions, as each recursive call
will be stored in the cache, but only the first iteration will be retrieved from
the cache; that is, the cache will be filled with many unreachable
entries. Instead, we recommend to perform a worker-wrapper transformation on
recursive functions, and apply the `memo` attribute to the wrapper.

**Warning:** A function declared with the `memo` attribute must not use
uninterpreted functions in the side-condition of any rule. Memoizing such an
impure function is unsound. To see why, consider the following rules:

```k
syntax Bool ::= impure( Int ) [function]

syntax Int ::= unsound( Int ) [function, memo]
rule unsound(X:Int) => X +Int 1 requires impure(X)
rule unsound(X:Int) => X        requires notBool impure(X)
```

Because the function `impure` is not given rules to cover all inputs, `unsound`
can be memoized incoherently. For example,

```
{unsound(0) #And {impure(0) #Equals true}} #Equals 1
```

but

```
{unsound(0) #And {impure(0) #Equals false}} #Equals 0
```

The memoized value of `unsound(0)` would be incoherently determined by which
pattern the backend encounters first.

### Variable Sort Inference

In K, it is not required that users declare the sorts of variables in rules or
in the initial configuration. If the user does not explicitly declare the sort
of a variable somewhere via a cast (see below), the sort of the variable is
inferred from context based on the sort signature of every place the variable
appears in the rule.

As an example, consider the rule for addition in IMP:

```k
    syntax Exp ::= Exp "+" Exp | Int

    rule I1 + I2 => I1 +Int I2
```

Here `+Int` is defined in the INT module with the following signature:

```k
    syntax Int ::= Int "+Int" Int [function]
```

In the rule above, the sort of both `I1` and `I2` is inferred as `Int`. This is because
a variable must have the same sort every place it appears within the same rule.
While a variable appearing only on the left-hand-side of the rule could have
sort `Exp` instead, the same variable appears as a child of `+Int`, which
constriants the sorts of `I1` and `I2` more tightly. Since the sort must be a
subsort of `Int` or equal to `Int`, and `Int` has no subsorts, we infer `Int`
 as the sorts of `I1` and `I2`. This means that the above rule will not match
until `I1` and `I2` become integers (i.e., have already been evaluated).

More complex examples are possible, however:

```k
    syntax Exp ::= Exp "+" Int | Int
    rule _ + _ => 0
```

Here we have two anonymous variables. They do not refer to the same variable
as one another, so they can have different sorts. The right side is constrained
by `+` to be of sort `Int`, but the left side could be either `Exp` or `Int`.
When this occurs, we have multiple solutions to the sorts of the variables in
the rule. K will only choose solutions which are **maximal**, however. To be
precise, if two different solutions exist, but the sorts of one solution are
all greater than or equal to the sorts of the other solution, K will discard
the smaller solution. Thus, in the case above, the variable on the left side
of the `+` is inferred of sort `Exp`, because the solution (`Exp`, `Int`) is
strictly greater than the solution (`Int`, `Int`).

It is possible, however, for terms to have multiple maximal solutions:

```k
    syntax Exp ::= Exp "+" Int | Int "+" Exp | Int
    rule I1 + I2 => 0
```

In this example, there is an ambiguous parse. This could parse as either
the first `+` or the second. In the first case, the maximal solution chosen is
(`Exp`, `Int`). In the second, it is (`Int`, `Exp`). Neither of these solutions is
greater than the other, so both are allowed by K. As a result, this program
will emit an error because the parse is ambiguous. To pick one solution over
the other, a cast or a `prefer` or `avoid` attribute can be used.

### Casting

There are three main types of casts in K: the semantic cast, the strict cast,
and the projection cast.

### Semantic casts

For every sort `S` declared in your grammar, K will define the following
production for you for use in rules:

```k
    syntax S ::= S ":S"
```

The meaning of this cast is that the term inside the cast must be less than
or equal to `Sort`. This can be used to resolve ambiguities, but its principle
purpose is to guide execution by telling K what sort variables must match in
order for the rule to apply. When compiled, it will generate a pattern that
matches on an injection into `Sort`.

### Strict casts

K also introduces the strict cast:

```k
    syntax S ::= S "::S"
```

The meaning at runtime is exactly the same as the semantic cast (except in the
ocaml backend, where it will match a term of any sort at runtime); however,
it restricts the sort of the term inside the cast to **exactly** `Sort`. That
is to say, if you use it on something that is a strictly smaller sort, it will
generate a type error. This is useful in certain circumstances to help
disambiguate terms, when a semantic cast would not have resolved the ambiguity.
As such, it is primarily used to solve ambiguities rather than to guide
execution.

### Projection casts

K also introduces the projection cast:

```k
    syntax {S2} S ::= "{" S2 "}" ":>S"
```

The meaning of this cast at runtime is that if the term inside is of sort
`Sort`, it should have it injection stripped away and the value inside is
returned as a term of static sort `Sort`. However, if the term is of a
different sort, it is an error and execution will get stuck. Thus the primary
usefulness of this cast is to cast the return value of a function with a
greater sort down to a strictly smaller sort that you expect the return value
of the function to have. For example:

```k
    syntax Exp ::= foo(Exp) [function] | bar(Int) | Int
    rule foo(I:Int) => I
    rule bar(I) => bar({foo(I +Int 1)}:>Int)
```

Here we know that `foo(I +Int 1)` will return an Int, but the return sort of
`foo` is `Exp`. So we project the result into the `Int` sort so that it can
be placed as the child of a `bar`.

### `owise` and `priority` attributes.

Sometimes, it is simply not convenient to explicitly describe every
single negative case under which a rule should **not** apply. Instead,
we simply wish to say that a rule should only apply after some other set of
rules have been tried. K introduces two different attributes that can be
added to rules which will automatically generate the necessary matching
conditions in a manner which is performant for concrete execution (indeed,
it generally outperforms during concrete execution code where the conditions
are written explicitly).

The first is the `owise` attribute. Very roughly, rules without an attribute
indicating their priority apply first, followed by rules with the `owise`
attribute only if all the other rules have been tried and failed. For example,
consider the following function:

```k
syntax Int ::= foo(Int) [function]
rule foo(0) => 0
rule foo(_) => 1 [owise]
```

Here `foo(0)` is defined explicitly as `0`. Any other integer yields the
integer `1`. In particular, the second rule above will only be tried after the
first rule has been shown not to apply.

This is because the first rule has a lower number assigned for its priority
than the second rule. In practice, each rule in your semantics is implicitly
or explicitly assigned a numerical priority. Rules are tried in increasing
order of priority, starting at zero and trying each increasing numerical value
successively.

You can specify the priority of a rule with the `priority` attribute. For
example, I could equivalently write the second rule above as:

```k
rule foo(_) => 1 [priority(200)]
```

The number `200` is not chosen at random. In fact, when you use the `owise`
attribute, what you are doing is implicitly setting the priority of the rule
to `200`. This has a couple of implications:

1. Multiple rules with the owise attribute all have the same priority and thus
   can apply in any order.
2. Rules with priority higher than `200` apply **after** all rules with the
   `owise` attribute have been tried.

There is one more rule by which priorities are assigned: a rule with no
attributes indicating its priority is assigned the priority 50. Thus,
with each priority explicitly declared, the above example looks like:

```k
syntax Int ::= foo(Int) [function]
rule foo(0) => 0 [priority(50)]
rule foo(_) => 1 [owise]
```

One final note: the llvm backend reserves priorities between 50 and 150
inclusive for certain specific purposes. Because of this, explicit
priorities which are given within this region may not behave precisely as
described above. This is primarily in order that it be possible where necessary
to provide guidance to the pattern matching algorithm when it would otherwise
make bad choices about which rules to try first. You generally should not
give any rule a priority within this region unless you know exactly what the
implications are with respect to how the llvm backend orders matches.


Evaluation Strategy
-------------------

### `strict` and `seqstrict` attributes

The strictness attributes allow defining evaluation strategies without having
to explicitely make rules which implement them. This is done by injecting
*heating* and *cooling* rules for the subterms. For this to work, you need to
define what a *result* is for K, by extending the  `KResult` sort.

For example:

```k
syntax AExp ::= Int
              | AExp "+" AExp [strict]
```

This generates two heating rules (where the hole syntaxes `"[]" "+" AExp` and
`AExp "+" "[]"` is automatically added to create an evaluation context):

```k
rule <k> HOLE:AExp +  AE2:AExp => HOLE ~>  [] + AE2 ... </k> [heat]
rule <k>  AE1:AExp + HOLE:AExp => HOLE ~> AE1 +  [] ... </k> [heat]
```

And two corresponding cooling rules:

```k
rule <k> HOLE:AExp ~>  [] + AE2 => HOLE +  AE2 ... </k> [cool]
rule <k> HOLE:AExp ~> AE1 +  [] =>  AE1 + HOLE ... </k> [cool]
```

You will note that these rules can apply one after another infinitely. In
practice, the `KResult` sort is used to break this cycle by ensuring that only
terms that are not part of the `KResult` sort will be heated. The `heat` and
`cool` attributes are used to tell the compiler that these are heating and
cooling rules and should be handled in the manner just described. Nothing stops
the user from writing such heating and cooling rules directly if they wish,
although we describe other more convenient syntax for most of the advanced
cases below.

One other thing to note is that in the above sentences, `HOLE` is just a
variable, but it has special meaning in the context of sentences with the
`heat` or `cool` attribute. In heating or cooling rules, the variable named
`HOLE` is considered to be the term being heated or cooled and the compiler
will generate `isKResult(HOLE)` and `notBool isKResult(HOLE)` side conditions
appropriately to ensure that the backend does not loop infinitely.

In order for this functionality to work, you need to define the `KResult` sort.
For instance, we tell K that a term is fully evaluated once it becomes an `Int`
here:

```k
syntax KResult ::= Int
```

Note that you can also say that a given expression is only strict only in
specific argument positions. Here we use this to define "short-circuiting"
boolean operators.

```k
syntax KResult ::= Bool

syntax BExp ::= Bool
              | BExp "||" BExp [strict(1)]
              | BExp "&&" BExp [strict(1)]

rule <k> true  || _    => true ... </k>
rule <k> false || REST => REST ... </k>

rule <k> true  && REST => REST  ... </k>
rule <k> false && _    => false ... </k>
```

If you want to force a specific evaluation order of the arguments, you can use
the variant `seqstrict` to do so. For example, this would make the boolean
operators short-circuit in their _second_ argument first:

```k
syntax KResult ::= Bool

syntax BExp ::= Bool
              | BExp "||" BExp [seqstrict(2,1)]
              | BExp "&&" BExp [seqstrict(2,1)]

rule <k> _    || true  => true ... </k>
rule <k> REST || false => REST ... </k>

rule <k> REST && true  => REST  ... </k>
rule <k> _    && false => false ... </k>
```

This will generate rules like this in the case of `_||_` (note that `BE1` will
not be heated unless `isKResult(BE2)` is true, meaning that `BE2` must be
evaluated first):

```k
rule <k>  BE1:BExp || HOLE:BExp => HOLE ~> BE1 ||  [] ... </k> [heat]
rule <k> HOLE:BExp ||  BE2:BExp => HOLE ~>  [] || BE2 ... </k> requires isKResult(BE2) [heat]

rule <k> HOLE:BExp ~>  [] || BE2 => HOLE ||  BE2 ... </k> [cool]
rule <k> HOLE:BExp ~> BE1 ||  [] =>  BE1 || HOLE ... </k> [cool]
```

### Context Declaration

Sometimes more advanced evaluation strategies are needed. By default, the
`strict` and `seqstrict` attributes are limited in that they cannot describe
the _context_ in which heating or cooling should occur. When this type of
control over the evaluation strategy is required, `context` sentences can be
used to simplify the process of declaring heating and cooling when it would be
unnecessarily verbose to write heating and cooling rules directly.

For example, if the user wants to heat a term if it exists under a `foo`
constructor if the term to be heated is of sort `bar`, one might write the
following context:

```k
context foo(HOLE:Bar)
```

Once again, note that `HOLE` is just a variable, but one that has special
meaning to the compiler indicating the position in the context that should
be heated or cooled.

This will automatically generate the following sentences:

```k
rule <k> foo(HOLE:Bar) => HOLE ~> foo([]) ... </k> [heat]
rule <k> HOLE:Bar ~> foo([]) => foo(HOLE) ... </k> [cool]
```

The user may also write the K cell explicitly in the context declaration
if they want to match on another cell as well, for example:

```k
context <k> foo(HOLE:Bar) ... </k> <state> .Map </state>
```

This context will now only heat or cool if the `state` cell is empty.

### Side conditions in context declarations

The user is allowed to write a side condition in a context declaration, like
so:

```k
context foo(HOLE:Bar) requires baz(HOLE)
```

This side condition will be appended verbatim to the heating rule that is
generated, however, it will not affect the cooling rule that is generated:

```k
rule <k> foo(HOLE:Bar) => HOLE ~> foo([]) ... </k> requires baz(HOLE) [heat]
rule <k> HOLE:Bar ~> foo([]) => foo(HOLE) ... </k> [cool]
```

### Rewrites in context declarations

The user can also include exactly one rewrite operation in a context
declaration if that rule rewrites the variable `HOLE` on the left hand side
to a term containing `HOLE` on the right hand side. For exampl;e:

```k
context foo(HOLE:Bar => bar(HOLE))
```

In this case, the code generated will be as follows:

```k
rule <k> foo(HOLE:Bar) => bar(HOLE) ~> foo([]) ... </k> [heat]
rule <k> bar(HOLE:Bar) ~> foo([]) => foo(HOLE) ... </k> [cool]
```

This can be useful if the user wishes to evaluate a term using a different
set of rules than normal.

### `result` attribute

Sometimes it is necessary to be able to evaluate a term to a different sort
than `KResult`. This is done by means of adding the `result` attribute to
a strict production, a context, or an explicit heating or cooling rule:

```k
syntax BExp ::= Bool
              | BExp "||" BExp [seqstrict(2,1), result(Bool)]
```

In this case, the sort check used by `seqstrict` and by the `heat` and `cool`
attributes will be `isBool` instead of `isKResult`. This particular example
does not really require use of the `result` attribute, but if the user wishes
to evaluate a term of sort KResult further, the result attribute would be
required.

### `hybrid` attribute

In certain situations, it is desirable to treat a particular production which
has the `strict` attribute as a result if the term has had its arguments fully
evaluated. This can be accomplished by means of the `hybrid` attribute:

```k
syntax KResult ::= Bool

syntax BExp ::= Bool
              | BExp "||" BExp [strict(1), hybrid]
```

This attribute is equivalent in this case to the following additional axiom
being added to the definition of `isKResult`:

```k
rule isKResult(BE1:BExp || BE2:BExp) => true requires isKResult(BE1)
```

Sometimes you wish to declare a production hybrid with respect to a predicate
other than `isKResult`. You can do this by specifying a sort as the body of the
`hybrid` attribute, e.g.:

```k
syntax BExp ::= BExp "||" BExp [strict(1), hybrid(Foo)]
```

generates the rule:

```k
rule isFoo(BE1:BExp || BE2:BExp) => true requires isFoo(BE1)
```

Properly speaking, `hybrid` takes an optional comma-separated list of sort
names. If the list is empty, the attribute is equivalent to `hybrid(KResult)`.
Otherwise, it generates hybrid predicates for exactly the sorts named.

### Context aliases

Sometimes it is necessary to define a fairly complicated evaluation strategy
for a lot of different operators. In this case, the user _could_ simply write
a number of complex `context` declarations, however, this quickly becomes
tedious. For this purpose, K has a concept called a _context alias_. A context
alias is a bit like a template for describing contexts. The template can then
be instantiated against particular productions using the `strict` and
`seqstrict` attributes.

Here is a (simplified) example taken from the K semantics of C++:

```k
context alias [c]: <k> HERE:K ... </k> <evaluate> false </evaluate>
context alias [c]: <k> HERE:K ... </k> <evaluate> true </evaluate> [result(ExecResult)]

syntax Expr ::= Expr "=" Init [strict(c; 1)]
```

This defines the evaluation strategy during the translation phase of a C++
program for the assignment operator. It is equivalent to writing the following
context declarations:

```k
context <k> HOLE:Expr = I:Init ... </k> <evaluate> false </evaluate>
context <k> HOLE:Expr = I:Init ... </k> <evaluate> true </evaluate> [result(ExecResult)]
```

What this is saying is, if the `evaluate` cell is false, evaluate the term
like normal to a `KResult`. But if the `evaluate` cell is true, instead
evaluate it to the `ExecResult` sort.

Essentially, we have given a name to this evaluation strategy in the form of
the rule label on the context alias sentences (in this case, `c`). We can
then say that we want to use this evaluation strategy to evaluate particular
arguments of particular productions by referring to it by name in a `strict`
attribute. For example, `strict(c)` will instantiate these contexts once for
each argument of the production, whereas `strict(c; 1)` will instantiate it
only for the first argument. The special variable `HERE` is used to tell the
compiler where you want to place the production that is to be heated or cooled.

You can also specify multiple context aliases for different parts of a production,
for example:

```k
syntax Exp ::= foo(Exp, Exp) [strict(left; 1; right; 2)]
```

This says that we can evaluate the left and right arguments in either order, but to evaluate
the left using the `left` context alias and the right using the `right` context alias.

We can also say `seqstrict(left; 1; right; 2)`, in which case we additionally must evaluate
the left argument before the right argument. Note, all strict positions are considered collectively
when determining the evaluation order of `seqstrict` or the `hybrid` predicates.

A `strict` attribute with no rule label associated with it is equivalent to
a `strict` attribute given with the following context alias:

```k
context alias [default]: <k> HERE:K ... </k>
```

One syntactic convenience that is provided is that if you wish to declare the following context:

```k
context foo(HOLE => bar(HOLE))
```

you can simply write the following:

```k
syntax Foo ::= foo(Bar) [strict(alias)]

context alias [alias]: HERE [context(bar)]
```


Pattern Matching
----------------

### As Patterns

New syntax has been added to K for matching a pattern and binding the resulting
match in its entirety to a variable.

The syntax is:

```
Pattern #as V::Var
```

In this case, Pattern, including any variables, is matched and the resulting
variables are added to the substitution if matching succeeds. Furthermore, the
term matched by Pattern is added to the substitution as V.

This code can also be used outside of any rewrite, in which case matching
occurs as if it appeared on the left hand side, and the right hand side becomes
a variable corresponding to the alias.

It is an error to use an as pattern on the right hand side of a rule.

### Record-like KApply Patterns

We have added a syntax for matching on KApply terms which mimics the record
syntax in functional languages. This allows us to more easily express patterns
involving a KApply term in which we don't care about some or most of the
children, without introducing a dependency into the code on the number of
arguments which could be changed by a future refactoring.

The syntax is:

```
record(... field1: Pattern1, field2: Pattern2)
```

Note that this only applies to productions that are prefix productions.
A prefix production is considered by the implementation to be any production
whose production items match the following regular expression:

```
(Terminal(_)*) Terminal("(")
(NonTerminal (Terminal(",") NonTerminal)* )?
Terminal(")")
```

In other words, any sequence of terminals followed by an open parenthesis, an
optional comma separated list of non-terminals, and a close parenthesis.

If a prefix production has no named nonterminals, a `record(...)` syntax is
allowed, but in order to reference specific fields, it is necessary to give one
or more of the non-terminals in the production names.

Note: because the implementation currently creates one production per possible
set of fields to match on, and because all possible permutations of all
possible subsets of a list of n elements is a number that scales factorially
and reaches over 100 thousand productions at n=8, we currently do not allow
fields to be matched in any order like a true record, but only in the same
order as appears in the production itself.

Given that this only reduces the number of productions to the size of the power
set, this will still explode the parsing time if we create large productions of
10 or more fields that all have names. This is something that should probably
be improved, however, productions with that large of an arity are rare, and
thus it has not been viewed as a priority.

### Or Patterns

Sometimes you wish to express that a rule should match if one out of multiple
patterns should match the same subterm. We can now express this in K by means
of using the `#Or` ML connective on the left hand side of a rule.

For example:

```k
rule foo #Or bar #Or baz => qux
```

Here any of foo, bar, or baz will match this rule. Note that the behavior is
ill-defined if it is not the case that all the clauses of the or have the same
bound variables.

### Matching global context in function rules

On occasion it is highly desirable to be able to look up information from the
global configuration and match against it when evaluating a function. For this
purpose, we introduce a new syntax for function rules.

This syntax allows the user to match on *function context* from within a
function rule:

```k
syntax Int ::= foo(Int) [function]

rule [[ foo(0) => I ]]
     <bar> I </bar>

rule something => foo(0)
```

This is completely desugared by the K frontend and does not require any special
support in the backend. It is an error to have a rewrite inside function
context, as we do not currently support propagating such changes back into the
global configuration. It is also an error if the context is not at the top
level of a rule body.

Desugared code:

```k
syntax Int ::= foo(Int, GeneratedTopCell) [function]

rule foo(0, <generatedTop>
              <bar> I </bar>
              ...
            </generatedTop> #as Configuration) => I
rule <generatedTop>
       <k> something ... </k>
       ...
     </generatedTop> #as Configuration
  => <generatedTop>
       <k> foo(0, Configuration> ... </k>
       ...
     </generatedTop>
```

### Collection patterns

It is allowed to write patterns on the left hand side of rules which refer to
complex terms of sort Map, List, and Set, despite these patterns ostensibly
breaking the rule that terms which are functions should not appear on the left
hand side of rules. Such terms are destructured into pattern matching
operations.

The following forms are allowed:

```
// 0 or more elements followed by 0 or 1 variables of sort List followed by
// 0 or more elements
ListItem(E1) ListItem(E2) L:List ListItem(E3) ListItem(E4)

// the empty list
.List

// 0 or more elements in any order plus 0 or 1 variables of sort Set
// in any order
SetItem(K1) SetItem(K2) S::Set SetItem(K3) SetItem(K4)

// the empty set
.Set

// 0 or more elements in any order plus by 0 or 1 variables of sort Map
// in any order
K1 |-> E1 K2 |-> E2 M::Map K3 |-> E3 K4 |-> E4

// the empty map
.Map
```

Here K1, K2, K3, K4 etc can be any pattern except a pattern containing both
function symbols and unbound variables. An unbound variable is a variable whose
binding cannot be determined by means of decomposing non-set-or-map patterns or
map elements whose keys contain no unbound variables.

This is determined recursively, ie, the term `K1 |-> E2 E2 |-> E3 E3 |-> E4` is
considered to contain no unbound variables.

Note that in the pattern `K1 |-> E2 K3 |-> E4 E4 |-> E5`, K1 and K3 are
unbound, but E4 is bound because it is bound by deconstructing the key E3, even
though E3 is itself unbound.

In the above examples, E1, E2, E3, and E4 can be any pattern that is normally
allowed on the lhs of a rule.

When a map or set key contains function symbols, we know that the variables in
that key are bound (because of the above restriction), so it is possible to
evaluate the function to a concrete term prior to performing the lookup.

Indeed, this is the precise semantics which occurs; the function is evaluated
and the result is looked up in the collection.

For example:

```k
syntax Int ::= f(Int) [function]
rule f(I:Int) => I +Int 1
rule <k> I:Int => . ... </k> <state> ... SetItem(f(I)) ... </state>
```

This will rewrite `I` to `.` if and only if the state cell contains
`I +Int 1`.

Note that in the case of Set and Map, one guarantee is that K1, K2, K3, and K4
represent /distinct/ elements. Pattern matching fails if the correct number of
distinct elements cannot be found.

### Matching on cell fragments

K allows matching fragments of the configuration and using them to construct
terms and use as function parameters.

```k
configuration <t>
                <k> #init ~> #collectOdd ~> $PGM </k>
                <fs>
                  <f multiplicity="*" type="Set"> 1 </f>
                </fs>
              </t>
```

The `#collectOdd` construct grabs the entire content of the `<fs>` cell.
We may also match on only a portion of its content. Note that the fragment
must be wrapped in a `<f>` cell at the call site.

```k
syntax KItem ::= "#collectOdd"
rule <k> #collectOdd => collectOdd(<fs> Fs </fs>) ... </k>
     <fs> Fs </fs>
```

The `collectOdd` function collects the items it needs

```k
syntax Set ::= collectOdd(FsCell) [function]
rule collectOdd(<fs> <f> I </f> REST </fs>) => SetItem(I) collectOdd(<fs> REST </fs>) requires I %Int 2 ==Int 1
rule collectOdd(<fs> <f> I </f> REST </fs>) =>            collectOdd(<fs> REST </fs>) requires I %Int 2 ==Int 0
rule collectOdd(<fs> .Bag </fs>) => .Set
```

### `all-path` and `one-path` attributes to distinguish reachability claims

As the Haskell backend can handle both one-path and all-path reachability
claims, but both these are encoded as rewrite rules in K, these attributes can
be used to clarify what kind of claim a rule is.

In addition of being able to annotate a rule with one of them
(if annotating with more at the same time, only one of them would be chosen),
one can also annotate whole modules, to give a default claim type for all rules
in that module.

Additionally, the Haskell backend introduces an extra command line option
for the K frontend, `--default-claim-type`, with possible values
`all-path` and `one-path` to allow choosing a default type for all
claims.

### Set Variables

#### Motivation

Set variables were introduced as part of Matching Mu Logic, the mathematical
foundations for K. In Matching Mu Logic, terms evaluate to sets of values.
This is useful for both capturing partiality (as in `3/0`) and capturing
non-determinism (as in `3 #Or 5`). Consequently, symbol interpretation is
extended to have a collective interpretation over sets of input values.

Usually, K rules are given using regular variables, which expect that the term
they match is both defined and has a unique interpretation.

However, it is sometimes useful to have simplification rules which work over
any kind of pattern, be it undefined or non-deterministic. This behavior can be
achieved by using set variables to stand for any kind of pattern.

#### Syntax

Any variable prefixed by `@` will be considered a set variable.

#### Example

Below is a simplification rule which motivated this extension:

```
  rule #Ceil(@I1:Int /Int @I2:Int) =>
    {(@I2 =/=Int 0) #Equals true} #And #Ceil(@I1) #And #Ceil(@I2)
    [anywhere]
```

This rule basically says that `@I1:Int /Int @I2:Int` is defined if `@I1` and
`@I2` are defined and `@I2` is not 0. Using sets variables here is important as
it allows the simplification rule to apply _any_ symbolic patterns, without
caring whether they are defined or not.

This allows simplifying the expression `#Ceil((A:Int /Int B:Int) / C:Int)` to:

```
{(C =/=Int 0) #Equals true} #And #Ceil(C) #And ({(B =/=Int 0) #Equals true}
#And #Ceil(B) #And #Ceil(A)`
```

See [kframework/kore#729](https://github.com/kframework/kore/issues/729) for
more details.

#### SMT Translation

K makes queries to an SMT solver (Z3) to discharge proof obligations when doing
symbolic execution. You can control how these queries are made using the
attributes `smtlib` and `smt-hook` on declared productions.

- `smt-hook(...)` allows you to specify a term in SMTLIB2 format which should
  be used to encode that production, and assumes that all symbols appearing in
  the term are already declared by the SMT solver.
- `smtlib(...)` allows you to declare a new SMT symbol to be used when that
  production is sent to Z3, and gives it _uninterpreted function_ semantics.

```k
syntax Int ::= "~Int" Int          [function, klabel(~Int_), symbol,
                                    smtlib(notInt)]
             | Int "^%Int" Int Int [function, klabel(_^%Int__), symbol,
                                    smt-hook((mod (^ #1 #2) #3))]
```

In the example above, we declare two productions `~Int_` and `_^%Int__`, and
tell the SMT solver to:

-   use uninterpreted function semantics for `~Int_` via SMTLIB2 symbol
    `notInt`, and
-   use the SMTLIB2 term `(mod (^ #1 #2) #3)` (where `#N` marks the `N`th
    production non-terminal argument positions) for `_^%Int__`, where `mod` and
    `^` already are declared by the SMT solver.

#### Caution

Set variables are currently only supported by the Haskell backend.
The use of rules with set variables should be sound for all other backends
which just execute by rewriting, however it might not be safe for backends
which want to guarantee coverage.

### Variables occurring only in the RHS of a rule

This section presents possible scenarios requiring variables to only appear in
the RHS of a rule.

#### Summary
Except for `?` variables and `!` (fresh) variables, which are
__required__ to only appear in the RHS of a rule, all other variables __must__
also appear in the LHS of a rule.  This restriction also applies to anonymous
variables; in particular, for claims, `?_` (not `_`) should be used in the RHS
to indicate that something changes but we don't care to what value.

To support specifying random-like behavior, the above restriction can be relaxed
by annotating a rule with the `unboundVariables` attribute whenever the rule
intentionally contains regular variables only occurring in the RHS.

#### Introduction

K uses question mark variables of the form `?X` to refer to
existential variables, and uses `ensures` to specify logical constraints on
those variables.
These variables are only allowed to appear in the RHS of a K rule.

If the rules represent rewrite (semantic) steps or verification claims,
then the `?` variables are existentially quantified at the top of the RHS;
otherwise, if they represent equations, the `?` variables are quantified at the
top of the entire rule.

Note that when both `?`-variables and regular variables are present,
regular variables are (implicitly) universally quantified on top of the rule
(already containing the existential quantifications).
This essentially makes all `?` variables depend on all regular variables.

All examples below are intended more for program verification /
symbolic execution, and thus concrete implementations might choose to ignore
them altogether or to provide ad-hoc implementations for them.

#### Example: Verification claims

Consider the following definition of a (transition) system:

```k
module A
  rule foo => true
  rule bar => true
  rule bar => false
endmodule
```

Consider also, the following specification of claims about the definition above:
```k
module A-SPEC
  rule [s1]: foo => ?X:Bool
  rule [s2]: foo =>  X:Bool  [unboundVariables(X)]
  rule [s3]: bar => ?X:Bool
  rule [s4]: bar =>  X:Bool  [unboundVariables(X)]
endmodule
```

##### One-path interpretation

- (s1) says that there exists a path from `foo` to some boolean, which is
  satisfied easily using the `foo => true` rule
- (s3) says the same thing about `bar` and can be satisfied by either of
  `bar => true` and `bar => false` rules
- (s2) and (s4) can be better understood by replacing them with instances for
  __each__ element of type `Bool`, which can be interpreted that
  both `true` and `false` are reachable from `foo` for (s2), or `bar` for (s4),
  respectively.
  + (s2) cannot be verified as we cannot find a path from `foo` to `false`.
  + (s4) can be verified by using `bar => true` to show `true` is reachable and
    `bar => false` to achieve the same thing for `false`

##### All-path interpretation

- (s1) says that all paths from `foo` will reach some boolean, which is
  satisfied by the `foo => true` rule and the lack of other rules for `foo`
- (s3) says the same thing about `bar` and can be satisfied by checking that
   both `bar => true` and `bar => false` end in a boolean, and there are no
   other rules for `bar`
- (s2) and (s4) can be better understood by replacing them with instances for
  __each__ element of type `Bool`, which can be interpreted that
  both `true` and `false` are reachable __in all paths__ originating in
  `foo` for (s2), or `bar` for (s4), respectively.
  This is a very strong claim, requiring that all paths originating in
  `foo` (`bar`) pass through __both__ `true` and `false`,
  so neither (s2) nor (s4) can be verified.

  Interestingly enough, adding a rule like `false => true` would make both
  (s2) and (s4) hold.

#### Example: Random Number Construct `rand()`

The random number construct `rand()` is a language construct which could be
easily conceived to be part of the syntax of a programming language:

```k
Exp ::= "rand" "(" ")"
```

The intended semantics of `rand()` is that it can rewrite to any integer in
a single step. This could be expressed as the following following infinitely
many rules.

```k
rule  rand() => 0
rule  rand() => 1
rule  rand() => 2
  ...    ...
rule rand() => (-1)
rule rand() => (-2)
  ...    ...
```

Since we need an instance of the rule for __every__ integer, one could summarize
the above infinitely many rules with the rule

```
rule rand() => I:Int [unboundVariables(I)]
```

Note that `I` occurs only in the RHS in the rule above, and thus the rule
needs the `unboundVariables(I)` attribute to signal that this is intentionally.

One can define variants of `rand()` by further constraining the output variable
as a precondition to the rule.

##### Rand-like examples

1. `randBounded(M,N)` can rewrite to any integer between `M` and `N`

    ```k
    syntax Exp ::= randBounded(Int, Int)
    rule randBounded(M, N) => I
      requires M <=Int I andBool I <=Int N
      [unboundVariables(I)]
    ```

1. `randInList(Is)` takes a list `Is` of items
   and can rewrite in one step to any item in `Is`.

    ```k
    syntax Exp ::= randInList (List)
    rule randInList(Is) => I
      requires I inList Is
      [unboundVariables(I)]
    ```

1. `randNotInList(Is)` takes a list `Is` of items
   and can rewrite in one step to any item _not_ in `Is`.

    ```k
    syntax Exp ::= randNotInList (List)
    rule randNotInList(Is) => I
      requires notBool(I inList Is)
      [unboundVariables(I)]
    ```

1. `randPrime()`, can rewrite to any _prime number_.

    ```k
    syntax Exp ::= randPrime ()
    rule randPrime() => X:Int
      requires isPrime(X)
      [unboundVariables(X)]
    ```

   where `isPrime(_)` is a predicate that can be defined in the usual way.

Note 1: all above are not function symbols, but language constructs.

Note 2: Currently the frontend does not allow rules with universally quantified
variables in the RHS which are not bound in the LHS.

Note 3. Allowing these rules in a concrete execution engine would require an
algorithm for generating concrete instances for such variables, satisfying the
given constraints; thus the `unboundVariables` attribute serves two purposes:
- to allow such rules to pass the variable checks, and
- to signal (concrete execution) backends that specialized algorithm would be
needed to instantiate these variables.

#### Example: Fresh Integer Construct `fresh(Is)`

The fresh integer construct `fresh(Is)` is a language construct.

```
Exp ::= ... | "fresh" "(" List{Int} ")"
```

The intended semantics of `fresh(Is)` is that it can always rewrite to an
integer that in not in `Is`.

Note that `fresh(Is)` and `randNotInList(Is)` are different; the former
does not _need_ to be able to rewrite to every integers not in `Is`,
while the latter requires so.

For example, it is _correct_ to implement `fresh(Is)` so it always returns the
smallest positive integer that is not in `Is`, but same implementation for
`randNotInList(Is)` might be considered _inadequate_.
In other words, there exist multiple correct implementations of `fresh(Is)`,
some of which may be deterministic, but there only exists a unique
implementation of `randNotInList(Is)`.
Finally, note that `randNotInList(Is)` is a _correct_ implementation
for `fresh(Is)`; Hence, concrete execution engines can choose to handle
such rules accordingly.

We use the following K syntax to define `fresh(Is)`

```k
syntax Exp ::= fresh (List{Int})
rule fresh(Is:List{Int}) => ?I:Int
  ensures notBool (?I inList{Int} Is)
```

A variant of this would be a `choiceInList(Is)` language construct which would
choose some number from a list:

```k
syntax Exp ::= choiceInList (List{Int})
rule choiceInList(Is:List{Int}) => ?I:Int
  ensures ?I inList{Int} Is
```

Note: This definition is different from one using a `!` variable to indicate
freshness because using `!` is just syntactic sugar for generating globally
unique instances and relies on a special configuration cell, and cannot be
constrained, while the `fresh` described here is local and can be constrained.
While the first is more appropriate for concrete execution, this might be
better for symbolic execution / program verification.

#### Example: Arbitrary Number (Unspecific Function) `arb()`

The function `arb()` is not a PL construct, but a mathematical function.
Therefore, its definition should not be interpreted as an execution step, but
rather as an equality.

The intended semantics of `arb()` is that it is an unspecified nullary function.
The exact return value of `arb()` is unspecified in the semantics but up to the
implementations.
However, being a mathematical function, `arb()` must return the same value in
any one implementation.

We do not need special frontend syntax to define `arb()`.
We only need to define it in the usual way as a function
(instead of a language construct), and provide no axioms for it.
The `functional` attribute ensures that the function is total, i.e.,
that it evaluates to precisely one value for each input.

##### Variants

There are many variants of `arb()`. For example, `arbInList(Is)` is
an unspecified function whose return value must be an element from `Is`.

Note that `arbInList(Is)` is different from `choiceInList(Is)`, because
`choiceInList(Is)` _transitions_ to an integer in `Is` (could be a different one
each time it is used), while `arbInList(Is)` _is equal to_ a (fixed)
integer not in `Is`.

W.r.t. the `arb` variants, we can use `?` variables and the `function`
annotation to signal that we're defining a function and the value of the
function is fixed, but non-determinate.

```k
syntax Int ::= arbInList(List{Int}) [function]
rule arbInList(Is:List{Int}) => ?I:Int
  ensures ?I inList{Int} Is
```

If elimination of existentials in equational rules is needed, one possible
approach would be through [Skolemization](https://en.wikipedia.org/wiki/Skolem_normal_form),
i.e., replacing the `?` variable with a new uninterpreted function depending
on the regular variables present in the function.

#### Example: Interval (Non-function Symbols) `interval()`

The symbol `interval(M,N)` is not a PL construct, nor a function in the
first-order sense, but a proper matching-logic symbol, whose interpretation is
in the powerset of its domain.
Its axioms will not use rewrites but equalities.

The intended semantics of `interval(M,N)` is that it equals the _set_ of
integers that are larger than or equal to `M` and smaller than or equal to `N`.

Since expressing the axiom for `interval` requires an an existential
quantification on the right-hand-side, thus making it a non-functional symbol
defined through an equation, using `?` variables might be confusing since their
usage would be different from that presented in the previous sections.

Hence, the proposal to support this would be to write this as a proper ML rule.
A possible syntax for this purpose would be:

```
eq  interval(M,N)
    ==
    #Exists X:Int .
        (X:Int #And { X >=Int M #Equals true } #And { X <=Int N #Equals true })
```

Additionally, the symbol declaration would require a special attribute to
signal the fact that it is not a constructor but a _defined_ symbol.

Since this feature is not clearly needed by K users at the moment, it is only
presented here as an example; its implementation will be postponed for such time
when its usefulness becomes apparent.


Parser Generation
-----------------

In addition to on-the-fly parser generation using `kast`, K is capable of
ahead-of-time parser generation of LR(1) or GLR parsers using Flex and Bison.
This can be done one of two different ways.

1. You can explicitly request for a particular parser to be generated by
   invoking `kast --gen-parser <outputFile>` or
   `kast --gen-glr-parser <outputFile>` respectively. `kast` will then create a
   parser based on the same command line flags that govern on-the-fly parsing,
   like `-s` to specify the starting sort, and `-m` to specify the module to
   parse under. By default, this generates a parser for the sort of the `$PGM`
   configuration variable in the main syntax module of the definition.
2. You can request that a specific set of parsers be generated for all the
   configuration variables of your definition by passing the
   `--gen-bison-parser` or `--gen-glr-bison-parser` flags to `kompile`.
   `kompile` will decide the sorts to use as start symbols based on the sorts
   in the configuration declaration for the configuration variables. The `$PGM`
   configuration variable will be generated based on the main syntax module
   of the definition. The user must explicitly annotate the configuration
   declaration with the other modules to use to parse the other configuration
   variables as attributes. For example, if I have the following cell in the
   configuration declaration: `<cell> foo($FOO:Foo, $BAR:Bar) </cell>`,
   One might annotate it with the attribute pair `parser="FOO, TEST; BAR, TEST2"`
   to indicate that configuration variable `$FOO` should be parsed in the
   `TEST` module, and configuration variable `$BAR` should be parsed in the
   `TEST2` module. If the user forgets to annotate the declaration with the
   parser attribute, only the `$PGM` parser will be generated.

Bison-generated parsers are extremely fast compared to `kast`, but they have
some important limitations:

* Bison parsers will always output Kore. You can then pass the resulting AST
  directly to `llvm-krun` or `kore-exec` and bypass the `krun` frontend, making
  them very fast, but lower-level.
* Bison parsers do not yet support macros. This may change in a future release.
  Note that you can use anywhere rules instead of macros in most cases to get
  around this limitation, although they will not benefit from unparsing via the
  `alias` attribute.
* Obligation falls on the user to ensure that the grammar they write is LR(1)
  if they choose to use LR(1) parsing. If this does not happen, the parser
  generated will have shift/reduce or reduce/reduce conflicts and the parser
  may behave differently than `kast` would (`kast` is a GLL parser, ie, it
  is based on LL parsers and parses all unambiguous context-free grammars).
  K provides an attribute, `not-lr1`, which can be applied to modules known to
  not be LR(1), and will trigger a warning if the user attempts to generate an
  LR(1) parser which recursively imports that module.
* If you are using LR(1) based parsing, the `prefer` and `avoid` attributes are
  ignored. It is only possible to implement these attributes by means of
  generalized LL or LR parsing and a postprocessing on the AST to remove the
  undesirable ambiguity.
* Obligation falls on the user to ensure that the grammar they write has as
  few conflicts as possible if they are using GLR parsing. Bison's GLR support
  is quite primitive, and in the worst case it can use exponential space and
  time to parse a program, which generally leads the generated parser to report
  "memory exhausted", indicating that the parse could not be completed within
  the stack space allocated by Bison. It's best to ensure that the grammar is
  as close to LR(1) as possible and only utilizes conflicts where absolutely
  necessary. One tool that can be used to facilitate this is to pass
  `--bison-lists` to kompile. This will disable support for the `List{Sort}`
  syntax production, and it will make `NeList{Sort}` left associative, but the
  resulting productions generated for `NeList{Sort}` will be LR(1) and use bounded
  stack space.
* If the grammar you are parsing is context-sensitive (for example, because
  it requires a symbol table to parse), one thing you can do to make this
  language parse in K is to implement the language as an ambiguous grammar.
  Bison's GLR parser will generate an `amb` production that is parametric in
  the sort of the ambiguity. You can then import the `K-AMBIGUITIES` module
  and use rewriting to resolve the ambiguities using whatever preprocessing
  mechanisms you prefer.


Location Information
--------------------

K is able to insert file, line, and column metadata into the parse tree on a
per-sort basis when parsing using a bison-generated parser. To enable this,
mark the sort with the `locations` attribute.

```k
  syntax Exp [locations]
  syntax Exp ::= Exp "/" Exp | Int
```

K implicitly wraps productions of these sorts in a `#location` term (see the
`K-LOCATIONS` module in `kast.md`). The metadata can thus be accessed with
ordinary rewrite rules:

```k
  rule #location(_ / 0, File, StartLine, _StartColumn, _EndLine, _EndColumn) =>
  "Error: Division by zero at " +String File +String ":" Int2String(StartLine)
```


Unparsing
---------

A number of factors go into how terms are unparsed in K. Here we describe some
of the features the user can use to control how unparsing happens.

### Brackets

One of the phases that the unparser goes through is to insert productions
tagged with the `bracket` attribute where it believes this is necessary
in order to create a correct string that will be parsed back into the original
AST. The most common case of this is in expression grammars. For example,
consider the following grammar:

```k
syntax Exp ::= Int
             | Exp "*" Exp
             > Exp "+" Exp
```

Here we have declared that expressions can contain integer addition and
multiplication, and that multiplication binds tighter than addition. As a
result, when writing a program, if we want to write an expression that first
applies addition, then multiplication, we must use brackets: `(1 + 2) * 3`.
Similarly, if we have such an AST, we must **insert** brackets into the AST
in order to faithfully unparse the term in a manner that will be parsed back
into the same ast, because if we do not, we end up unparsing the term as
`1 + 2 * 3`, which will be parsed back as `1 + (2 * 3)` because of the priority
declaration in the grammar.

You can control how the unparser will insert such brackets by adding a
production with the `bracket` attribute and the correct sort. For example, if,
instead of parentheses, you want to use curly braces, you could write:

```k
syntax Exp ::= "{" Exp "}" [bracket]
```

This would signal to the unparser how brackets should look for terms of sort
`Exp`, and it will use this syntax when unparsing terms of sort `Exp`.

### Commutative collections

One thing that K will do (unless you pass the `--no-sort-collections` flag to
krun) is to sort associative, commutative collections (such as `Set` and `Map`)
alphanumerically. For example, if I have a collection whose keys are sort `Id`
and they have the values a, b, c, and d, then unparsing will always print
first the key a, then b, then c, then d, because this is the alphabetic order
of these keys when unparsed.

Furthermore, K will sort numeric keys numerically. For example, if I have a
collection whose keys are `1, 2, 5, 10, 30`, it will first display 1, then 2,
then 5, then 10, then 30, because it will sort these keys numerically. Note
that this is different than an alphabetic sort, which would sort them as
`1, 10, 2, 30, 5`. We believe the former is more intuitive to users.

### Substitution filtering

K will remove substitution terms corresponding to anonymous variables when
using the `--pattern` flag if those anonymous variables provide no information
about the named variables in your serach pattern. You can disable this behavior
by passing `--no-substitution-filtering` to krun. When this flag is not passed,
and you are using the Haskell backend, any equality in a substitution (ie, an
`#Equals` under an `#And` under an `#Or`), will be hidden from the user if the
left hand side is a variable that was anonymous in the `--pattern` passed by
the user, unless that variable appears elsewhere in the substitution. If you
want to see that variable in the substitution, you can either disable this
filtering, or give that variable a name in the original search pattern.

### Variable alpha renaming

K will automatically rename variables that appear in the output configuration.
Similar to commutative collections, this is done to **normalize** the resulting
configuration so that equivalent configurations will be printed identically
regardless of how they happen to be reached. This pass can be disabled by
passing `--no-alpha-renaming` to krun.

### Macro expansion

K will apply macros in reverse on the output configuration if the macro was
created with the `alias` or `alias-rec` attribute. See the section on macro
expansion for more details.

### Formatting

#### `format` attribute

K allows you to control how terms are unparsed using the `format` attribute.
By default, a domain value is unparsed by printing its string value verbatim,
and an application pattern is unparsed by printing its terminals and children
in the sequence implied by its concrete syntax, separated by spaces. However,
K gives you complete control over how you want to unparse the symbol.

A format attribute is a string containing zero or more escape sequences that
tell K how to unparse the symbol. Escape sequences begin with a '%' and are
followed by either an integer, or a single non-digit character. Below is a
list of escape sequences recognized by the formatter:

| Escape Sequence | Meaning                                                   |
| --------------- | --------------------------------------------------------- |
| n               | Insert '\n' followed by the current indentation level     |
| i               | Increase the current indentation level by 1               |
| d               | Decrease the current indentation level by 1               |
| c               | Move to the next color in the list of colors for this
                    production                                                |
| r               | Reset color to the default foreground color for the
                    terminal                                                  |
| an integer      | Print a terminal or nonterminal from the production.
                    The integer is treated as a 1-based index into the
                    terminals and nonterminals of the production.

                    If the offset refers to a terminal, move to the next color
                    in the list of colors for this production, print the value
                    of that terminal, then reset the color to the default
                    foreground color for the terminal.

                    If the offset refers to a regular expression terminal, it
                    is an error.

                    If the offset refers to a nonterminal, print the unparsed
                    representation of the corresponding child of the current
                    term.                                                     |
| any other char  | Print that character verbatim                             |

For more information on how colors work, see below.

#### `color` and `colors` attributes

K allows you to take advantage of ANSI terminal codes for foreground color
in order to colorize output pretty-printed by the unparser. This is controlled
via the `color` and `colors` attributes of productions. These attributes
combine with the `format` attribute to control how a term is colorized.

The first thing to understand about how colorization works is that the `color`
and `colors` attributes are used to construct a **list** of colors associated
with each production, and the format attribute then uses that list to choose
the color for each part of the production. For more information on how the
format attribute chooses a color from the list, see above, but essentially,
each terminal or `%c` in the format attribute advances the pointer in the list
by one element, and terminals and `%r` reset the current color to the default
foreground color of the terminal afterwards.

There are two ways you can construct a list of colors associated with a
production:

* The `color` attribute creates the entire list all with the same color, as
specified by the value of the attribute. When combined with the default format
attribute, this will color all the terminals in that production that color, but
more advanced techniques can be used as well.

* The `colors` attribute creates the list from a manual, comma-separated list
of colors. The attribute is invalid if the length of the list is not equal to
the number of terminals in the production plus the number of `%c` substrings in
the `format` attribute.


Debugging
---------

The LLVM Backend has support for integration with GDB. You can run the debugger
on a particular program by passing the `--debugger` flag to krun, or by
invoking the llvm backend interpreter directly. Below we provide a simple
tutorial to explain some of the basic commands supported by the LLVM backend.

### The K Definition

Here is a sample K definition we will use to demonstrate debugging
capabilities:

```k
module TEST
  imports INT

  configuration <k> foo(5) </k>
  rule [test]: I:Int => I +Int 1 requires I <Int 10

  syntax Int ::= foo(Int) [function]
  rule foo(I) => 0 -Int I

endmodule
```

You should compile this definition with `--backend llvm -ccopt -g` and without
`-ccopt -O2` in order to use the debugger most effectively.

### Stepping

**Important:** When you first run `krun` with option `--debugger`, GDB will
instruct you on how to modify ~/.gdbinit to enable printing abstract syntax
of K terms in the debugger. If you do not perform this step, you can still
use all the other features, but K terms will be printed as their raw address
in memory.

You can break before every step of execution is taken by setting a breakpoint
on the `step` function:

```
(gdb) break definition.kore:step
Breakpoint 1 at 0x25e340
(gdb) run
Breakpoint 1, 0x000000000025e340 in step (subject=`<generatedTop>{}`(`<k>{}`(`kseq{}`(`inj{Int{}, KItem{}}`(#token("0", "Int")),dotk{}(.KList))),`<generatedCounter>{}`(#token("0", "Int"))))
(gdb) continue
Continuing.

Breakpoint 1, 0x000000000025e340 in step (subject=`<generatedTop>{}`(`<k>{}`(`kseq{}`(`inj{Int{}, KItem{}}`(#token("1", "Int")),dotk{}(.KList))),`<generatedCounter>{}`(#token("0", "Int"))))
(gdb) continue 2
Will ignore next crossing of breakpoint 1.  Continuing.

Breakpoint 1, 0x000000000025e340 in step (subject=`<generatedTop>{}`(`<k>{}`(`kseq{}`(`inj{Int{}, KItem{}}`(#token("3", "Int")),dotk{}(.KList))),`<generatedCounter>{}`(#token("0", "Int"))))
(gdb)
```

### Breaking on a specific rule

You can break when a rule is applied by giving the rule a rule label. If the
module name is TEST and the rule label is test, you can break when the rule
applies by setting a breakpoint on the `TEST.test.rhs` function:

```
(gdb) break TEST.test.rhs
Breakpoint 1 at 0x25e250: file /home/dwightguth/test/./test.k, line 4.
(gdb) run
Breakpoint 1, TEST.test.rhs (VarDotVar0=`<generatedCounter>{}`(#token("0", "Int")), VarDotVar1=dotk{}(.KList), VarI=#token("0", "Int")) at /home/dwightguth/test/./test.k:4
4         rule [test]: I:Int => I +Int 1 requires I <Int 10
(gdb)
```

Note that the substitution associated with that rule is visible in the
description of the frame.

You can also break when a side condition is applied using the `TEST.test.sc`
function:

```
(gdb) break TEST.test.sc
Breakpoint 1 at 0x25e230: file /home/dwightguth/test/./test.k, line 4.
(gdb) run
Breakpoint 1, TEST.test.sc (VarI=#token("0", "Int")) at /home/dwightguth/test/./test.k:4
4         rule [test]: I:Int => I +Int 1 requires I <Int 10
(gdb)
```

Note that every variable used in the side condition can have its value
inspected when stopped at this breakpoint, but other variables are not visible.

You can also break on a rule by its location:

```
(gdb) break test.k:4
Breakpoint 1 at 0x25e230: test.k:4. (2 locations)
(gdb) run
Breakpoint 1, TEST.test.sc (VarI=#token("0", "Int")) at /home/dwightguth/test/./test.k:4
4         rule [test]: I:Int => I +Int 1 requires I <Int 10
(gdb) continue
Continuing.

Breakpoint 1, TEST.test.rhs (VarDotVar0=`<generatedCounter>{}`(#token("0", "Int")), VarDotVar1=dotk{}(.KList), VarI=#token("0", "Int")) at /home/dwightguth/test/./test.k:4
4         rule [test]: I:Int => I +Int 1 requires I <Int 10
(gdb) continue
Continuing.

Breakpoint 1, TEST.test.sc (VarI=#token("1", "Int")) at /home/dwightguth/test/./test.k:4
4         rule [test]: I:Int => I +Int 1 requires I <Int 10
(gdb)
```

Note that this sets a breakpoint at two locations: one on the side condition
and one on the right hand side. If the rule had no side condition, the first
would not be set. You can also view the locations of the breakpoints and
disable them individually:

```
(gdb) info breakpoint
Num     Type           Disp Enb Address            What
1       breakpoint     keep y   <MULTIPLE>
        breakpoint already hit 3 times
1.1                         y     0x000000000025e230 in TEST.test.sc at /home/dwightguth/test/./test.k:4
1.2                         y     0x000000000025e250 in TEST.test.rhs at /home/dwightguth/test/./test.k:4
(gdb) disable 1.1
(gdb) continue
Continuing.

Breakpoint 1, TEST.test.rhs (VarDotVar0=`<generatedCounter>{}`(#token("0", "Int")), VarDotVar1=dotk{}(.KList), VarI=#token("1", "Int")) at /home/dwightguth/test/./test.k:4
4         rule [test]: I:Int => I +Int 1 requires I <Int 10
(gdb) continue
Continuing.

Breakpoint 1, TEST.test.rhs (VarDotVar0=`<generatedCounter>{}`(#token("0", "Int")), VarDotVar1=dotk{}(.KList), VarI=#token("2", "Int")) at /home/dwightguth/test/./test.k:4
4         rule [test]: I:Int => I +Int 1 requires I <Int 10
(gdb)
```

Now only the breakpoint when the rule applies is enabled.

### Breaking on a function

You can also break when a particular function in your semantics is invoked:

```
(gdb) info functions foo
All functions matching regular expression "foo":

File /home/dwightguth/test/./test.k:
struct __mpz_struct *Lblfoo'LParUndsRParUnds'TEST'UndsUnds'Int(struct __mpz_struct *);
(gdb) break Lblfoo'LParUndsRParUnds'TEST'UndsUnds'Int
Breakpoint 1 at 0x25e640: file /home/dwightguth/test/./test.k, line 6.
(gdb) run
Breakpoint 1, Lblfoo'LParUndsRParUnds'TEST'UndsUnds'Int (_1=#token("1", "Int")) at /home/dwightguth/test/./test.k:6
6         syntax Int ::= foo(Int) [function]
(gdb)
```

In this case, the variables have numbers instead of names because the names of
arguments in functions in K come from rules, and we are stopped before any
specific rule has applied. For example, `_1` is the first argument to the
function.

You can also set a breakpoint in this location by setting it on the line
associated with its production:

```
(gdb) break test.k:6
Breakpoint 1 at 0x25e640: file /home/dwightguth/test/./test.k, line 6.
(gdb) run
Breakpoint 1, Lblfoo'LParUndsRParUnds'TEST'UndsUnds'Int (_1=#token("1", "Int")) at /home/dwightguth/test/./test.k:6
6         syntax Int ::= foo(Int) [function]
```

These two syntaxes are equivalent; use whichever is easier for you.

You can also view the stack of function applications:

```
(gdb) bt
#0  Lblfoo'LParUndsRParUnds'TEST'UndsUnds'Int (_1=#token("1", "Int")) at /home/dwightguth/test/./test.k:6
#1  0x000000000025e5f8 in apply_rule_111 (VarDotVar0=`<generatedCounter>{}`(#token("0", "Int")), VarDotVar1=dotk{}(.KList)) at /home/dwightguth/test/./test.k:9
#2  0x0000000000268a52 in take_steps ()
#3  0x000000000026b7b4 in main ()
(gdb)
```

Here we see that `foo` was invoked while applying the rule on line 9 of test.k,
and we also can see the substitution of that rule. If foo was evaluated while
evaluating another function, we would also be able to see the arguments of that
function as well, unless the function was tail recursive, in which case no
stack frame would exist once the tail call was performed.

### Breaking on a set of rules or functions

Using `rbreak <regex>` you can set breakpoints on multiple functions.

-   `rbreak Lbl` - sets a breakpoint on all non hooked `function`s

-   `rbreak Lbl.*TEST` - sets a breakpoint on all `function`s from module `TEST`

-   `rbreak hook_INT` - sets a breakpoint on all hooks from module `INT`

### Other debugger issues

-   `<optimized out>` try kompiling without `-O1`, `-O2`, or `-O3`.
-   `(gdb) break definition.kore:break -> No source file named definition.kore.`
send `-ccopt -g` to kompile in order to generate debug info symbols.


Pending Documentation
---------------------

Backend features not yet given documentation:

* Parser of KORE terms and definitions
* Term representation of K terms
* Hooked sorts and symbols
* Substituting a substitution into the RHS of a rule
  * domain values
  * functions
  * variables
  * symbols
  * polymorphism
  * hooks
  * injection compaction
  * overload compaction
* Pattern Matching / Unification of subject and LHS of rule
  * domain values
  * symbols
  * side conditions
  * and/or patterns
  * list patterns
  * nonlinear variables
  * map/set patterns
    * deterministic
    * nondeterministic
  * modulo injections
  * modulo overloads
* Stepping
  * initialization
  * termination
* Print kore terms
* Equality/comparison of terms
* Owise rules
* Strategy #STUCK axiom
* User substitution
  * binders
  * kvar

To get a complete list of hooks supported by K, you can run:

```
grep -P -R "(?<=[^-])hook\([^)]*\)" k-distribution/include/kframework/builtin/ \
     --include "*.k" -ho | \
sed 's/hook(//' | sed 's/)//' | sort | uniq | grep -v org.kframework
```

All of these hooks will also eventually need documentation.
