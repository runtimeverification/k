---
copyright: Copyright (c) Runtime Verification, Inc. All Rights Reserved.
---

# Lesson 1.3: BNF Syntax and Parser Generation

In this lesson we will introduce more key aspects of the syntax and 
semantics of **productions** in K, and show how these, along with other 
syntactic **sentences** can be used to define grammars for parsing both rules 
and programs. In this context, you'll also learn about two additional types
of productions, **brakets** and **tokens**.

## K's approach to parsing

K's grammar is divided into two components: the **outer syntax** of K and the
**inner syntax** of K. Outer syntax refers to the parsing of **requires**,
**modules**, **imports**, and **sentences** in a K definition. Inner syntax
refers to the parsing of **rules** and **programs**. Unlike the outer syntax of
K, which is predetermined, much of the inner syntax of K is defined by you, the
developer. When rules or programs are parsed, they are parsed within the
context of a module. Rules are parsed in the context of the module in which
they exist, whereas programs are parsed in the context of the
**main syntax module** of a K definition. 

Recall that a K definition consists of several modules, which in turn consist
each of several sentences (productions, rules, etc.). Sentences within a
module form the grammar of that module, and this grammar is used for parsing 
programs in the language you defined.

## Basic BNF productions

To illustrate how this works, let's consider the K module below which defines
a calculator for evaluating Boolean expressions containing operations AND, OR, 
NOT, and XOR.

Save the code below in file `lesson-03-a.k`:

```k
module LESSON-03-A

  syntax Boolean ::= "true" | "false"
                   | "!" Boolean [function]
                   | Boolean "&&" Boolean [function]
                   | Boolean "^" Boolean [function]
                   | Boolean "||" Boolean [function]

endmodule
```

Observe that the productions in this module look a little different than
what we have seen in the previous lesson. The reason is that K has two 
mechanisms for defining productions. A more generic one using a variant
of [BNF notation](https://en.wikipedia.org/wiki/Backus%E2%80%93Naur_form)
and its special case we have seen in [Lesson 1.2](../02_basics/README.md). 
There the `::=` symbol was followed by an alphanumeric identifier and a 
(possibly empty) comma-separated list of sorts in parentheses. In this 
lesson, we focus on the former.

Recall the set of productions from the previous lesson:

```k
module LESSON-03-B

  syntax Color ::= Yellow() | Blue()
  syntax Fruit ::= Banana() | Blueberry()
  syntax Color ::= colorOf(Fruit) [function]

endmodule
```

We can write an equivalent definition in BNF notation as follows:

```k
module LESSON-03-C

  syntax Color ::= "Yellow" "(" ")" | "Blue" "(" ")"
  syntax Fruit ::= "Banana" "(" ")" | "Blueberrry" "(" ")"
  syntax Color ::= "colorOf" "(" Fruit ")" [function]

endmodule
```

Note that sort `Fruit` of the function's argument is unchanged, but
everything else has been wrapped in double quotation marks. This is because
in BNF notation, we distinguish between two types of **production items**:
**terminals** and **non-terminals**. A terminal denotes a fixed sequence of
characters that is a verbatim part of the syntax of that production. For 
example, `Banana`, `(`, `)`, or `colorOf` are such sequences of characters and 
all considered terminals. Conversely, non-terminals, refer to a sort name, 
like `Fruit`, and the syntax of the production they belong to accepts any valid
term of that sort at that position.

In the previous lesson we executed successfully the program `colorOf(Banana())`
using `krun`. That is because the program represented a term of sort `Color`:
indeed, `Banana()` is a term of sort `Fruit`, hence a valid argument for 
function `colorOf`. `krun` parses and interprets terms according to the grammar
you define. Under the hood, the term is automatically converted into an AST 
(abstract syntax tree), and then the function `colorOf` is evaluated using the 
function rules provided in the definition.

How does K match the strings between the double quotes? The answer is that K 
uses [Flex](https://github.com/westes/flex) to generate a 
scanner for the grammar. Remember that a scanner, or lexical analyzer or lexer, 
is a component of an interpreter that breaks down source code into tokens, 
which are units such as keywords, variables, and operators. These tokens are 
then processed by the parser, which interprets the structure of the code 
according to the grammar rules. Flex looks for the longest possible match of a 
regular expression in the input. If there are ambiguities between two or more 
regular expressions, it will pick the one with the highest `prec` attribute. 
You can learn more about how Flex matching works in the 
[Flex Manual | Matching](https://westes.github.io/flex/manual/Matching.html#Matching).

Returning to module `LESSON-03-A`, we can see that it defines a simple BNF 
grammar for expressions over Booleans. We have defined constructors 
corresponding to the Boolean values _true_ and _false_, and functions 
corresponding to the Boolean operators AND, OR, NOT, and XOR. We have also 
given a syntax for each of these functions based on their syntax in the `C` 
programming language. As such, we can now write programs in the simple language 
we have defined!

Save the code below in file  `and.bool`:

```
true && false
```

Now, let's compile our grammar first:

```
kompile lesson-03-a.k
```

Recall that compilation produces a parser, interpreter, and verifier for the 
grammar specified in the K definition. Interpreting the program by executing

```
krun and.bool
```

will raise an error:

```
terminate called after throwing an instance of 'std::runtime_error'
  what():  No tag found for symbol Lbl'UndsAnd-And-UndsUnds'LESSON-03-A'Unds'Boolean'Unds'Boolean'Unds'Boolean{}. Maybe attempted to evaluate a symbol with no rules?

/nix/store/2av44963lcqsmkj7hwmjhrg9pzpbkr1i-k-7.1.232-88c9c766d76f624329400cd554fafd3beec16a15/bin-unwrapped/../lib/kframework/k-util.sh: line 114: 384286 Aborted                 (core dumped) "$@"
[Error] krun: ./lesson-03-a-kompiled/interpreter 
/tmp/.krun-2025-04-29-12-58-55-lb8wwXcWVv/tmp.in.0nVZCuXTXv -1 
/tmp/.krun-2025-04-29-12-58-55-lb8wwXcWVv/result.kore
Syntax error at /tmp/.krun-2025-04-29-12-58-55-lb8wwXcWVv/result.kore:1.1: Expected: [<id>, <string>] Actual: <EOF>
[Error] krun: kore-print --definition ./lesson-03-a-kompiled --output pretty 
/tmp/.krun-2025-04-29-12-58-55-lb8wwXcWVv/result.kore --color on
```

This is expected, as we have not given rules defining the meaning of the `&&` 
function, and the error message highlights exactly this&mdash;_Maybe attempted 
to evaluate a symbol with no rules?_ 

While we cannot interpret the program just yet, we can _parse_ it. To do this, 
run the command below from the same directory:

```
kast --output kore and.bool
```

You should see the following AST printed on standard output, minus the 
formatting:

```
inj{SortBoolean{}, SortKItem{}}(
  Lbl'UndsAnd-And-UndsUnds'LESSON-03-A'Unds'Boolean'Unds'Boolean'Unds'Boolean{}(
    Lbltrue'Unds'LESSON-03-A'Unds'Boolean{}(),
    Lblfalse'Unds'LESSON-03-A'Unds'Boolean{}()
  )
)
```

`kast` is K's just-in-time parser, just another tool generated at compile time. 
It produces a grammar from the K definition on the fly and uses it to parse 
the program passed on the command line. 

K allows for several AST representations and you can choose a specific one by
setting the `--output` flag. You can see all possible value options by running 
`kast --help`. `kore` used above is one of them and denotes KORE, the 
intermediate representation of K. You can learn more about KORE in another
[tutorial](https://github.com/runtimeverification/haskell-backend/blob/master/docs/kore-syntax.md), 
currently work-in-progress.
Value `kast` for the flag gives us an AST in a more direct representation of 
the original K definition.

Executing

```
kast --output kast and.bool
```

yields the following output, minus the formatting:

```
`_&&__LESSON-03-A_Boolean_Boolean_Boolean`(
  `true_LESSON-03-A_Boolean`(.KList),
  `false_LESSON-03-A_Boolean`(.KList)
)
```

Comparing both outputs, you can observe that the former is largely a 
name-mangled version of the latter. A notable difference is the presence of the
`inj` symbol in the KORE output and you can learn more about it in the
[KORE tutorial](https://github.com/runtimeverification/haskell-backend/blob/master/docs/kore-syntax.md).

Note that `kast` also takes expressions as arguments, not only file names, 
but not both at the same time. If you want to parse an expression, you need to
use flag `-e` or `--expression`:

```
kast --output kast -e "true && false"
```

### Exercise

Parse the expression `false || true` with `--output kast`. See if you can
predict approximately what the corresponding output would be with
`--output kore`, then run the command and compare it to your prediction.

## Ambiguities

Now let's try a slightly more advanced example. Save the following program as 
`and-or.bool`:

```
true && false || false
```

If you try to parse it, you will see the following error:

```
[Error] Inner Parser: Parsing ambiguity.
1: syntax Boolean ::= Boolean "&&" Boolean [function]
    `_&&__LESSON-03-A_Boolean_Boolean_Boolean`(`true_LESSON-03-A_Boolean`(.KList),`_||__LESSON-03-A_Boolean_Boolean_Boolean`(`false_LESSON-03-A_Boolean`(.KList),`false_LESSON-03-A_Boolean`(.KList)))
2: syntax Boolean ::= Boolean "||" Boolean [function]
    `_||__LESSON-03-A_Boolean_Boolean_Boolean`(`_&&__LESSON-03-A_Boolean_Boolean_Boolean`(`true_LESSON-03-A_Boolean`(.KList),`false_LESSON-03-A_Boolean`(.KList)),`false_LESSON-03-A_Boolean`(.KList))
	Source(./and-or.bool)
	Location(1,1,1,23)
	1 |	true && false || false
	  .	^~~~~~~~~~~~~~~~~~~~~~
```

The error is saying that `kast` was unable to parse the program because it is
ambiguous. K's just-in-time parser is a GLL (<u>g</u>eneralized 
<u>l</u>eft-to-right, <u>l</u>eftmost derivation) parser, which means it can handle
the full generality of context-free grammars, including those grammars which
are ambiguous. An ambiguous grammar is one where the same string can be parsed
as multiple distinct ASTs. In this example, it can't decide whether it should
be parsed as `(true && false) || false` (Fig. 3-A) or as `true && (false || false)`
(Fig. 3-B). 

Fig. 3-A
```
         ||
       /    \
     &&    false
   /    \
true   false
```

Fig. 3-B
```
    &&
  /    \
true    ||              
      /    \
   false  false    
```

In Boolean logic and other programming languages such as C, logical AND has 
precedence over logical OR, rendering the AST in Fig. 3-A the only valid one. 
However, grammars defined in K assume all operators to have the same priority 
in evaluation, unless specified otherwise. Both ASTs in Fig. 3-A and Fig. 3-B
are possible with the grammar we defined in module `LESSON-3-A`, hence the 
ambiguity reported by the parser. You will learn in the next lesson how to set 
up precendence of some operators over others and define the logical connectives 
_the usual way_. We continue this lesson by showing how to reduce ambiguity 
through the use of **brackets**.


## Brackets

With the grammar defined in module `LESSON-03-A` there is no way of resolving 
this ambiguity, making it impossible to write complex expressions in our small 
language. The standard solution in most programming languages to this problem 
is to use parentheses to indicate the appropriate grouping. K generalizes this 
notion into a type of production called **bracket**. 

A bracket production is any production with the `bracket` attribute. It is 
required that such a production only have a single non-terminal, and the sort 
of the production must equal the sort of that non-terminal. K does not
otherwise impose any restrictions on the grammar provided for a bracket. 

Like in other languages, the most common type of bracket is one in which a 
non-terminal is surrounded by terminals representing one of the following
symbols `()`, `[]`, `{}`, or `<>`. For example, we can define the most common
type of bracket, the parentheses, quite simply. Consider the following modified 
definition and save it to file `lesson-03-d.k`:

```k 
module LESSON-03-D

  syntax Boolean ::= "true" | "false"
                   | "(" Boolean ")" [bracket]
                   | "!" Boolean [function]
                   | Boolean "&&" Boolean [function]
                   | Boolean "^" Boolean [function]
                   | Boolean "||" Boolean [function]

endmodule
```

With this augmented definition, you are now able to parse more complex programs 
by explicitly grouping subterms with the bracket we have just defined.

Consider `and-or-left.bool`:

```
(true && false) || false
```

and `and-or-right.bool`:

```
true && (false || false)
```

When parsing these programs with `kast`, you get a unique AST with no error. 
If you check the output carefully, you will notice that the bracket itself does 
not appear in the AST. In fact, this is a property unique to bracket 
productions: they are not represented in the parsed AST of a term, and the 
child of the bracket is folded immediately into the parent term. This is why we 
have the requirement mentioned above, that a bracket production must have a 
single non-terminal of the same sort as the production itself.

### Exercise

Write out the AST you expect to be arising from parsing the two programs above 
with `--output kast`, then parse them and compare the result to the AST you 
expected. Confirm for yourself that the bracket production does not appear in 
the AST.

## Tokens

So far we have seen how to define the grammar of a language and we have 
implicitly been using K's automatic lexer generation to produce a token for 
each terminal in our grammar. However, the grammar is not the only relevant 
part of parsing a language. Also relevant is the lexical syntax of the 
language, i.e., how the tokens are defined and recognized. 

Sometimes we need to define more complex lexical syntax. Consider, for 
instance, integers in C. They consist of a decimal, octal, or hexadecimal 
number, followed by an optional suffix that specifies the type of the literal. 
While it’s theoretically possible to define this syntax using a grammar, doing 
so would be cumbersome and tedious. Additionally, you'd be faced with an AST 
generated for the literal, which is not particularly convenient to work with. 
As an alternative, K allows you to define **token** productions, which consist
of a [regular expressions](https://en.wikipedia.org/wiki/Regular_expression) 
followed by the `token` attribute. The resulting AST would then consist of a 
typed string containing the value recognized by the regular expression.

For example, the built-in integers in K are defined using the following
production:

```{.k .exclude}
syntax Int ::= r"[\\+\\-]?[0-9]+" [token]
```

An integer is thus an optional sign followed by a nonzero sequence of digits. 
The `r` preceding the terminal indicates that what appears inside the double 
quotes is a regular expression, and the `token` attribute indicates that terms 
which parse as this production should be converted into a token.

Before looking at how integers in C can be defined in K, let us mention that it
is also possible to define tokens that do not use regular expressions. This can 
be useful when you wish to declare particular identifiers for use in your 
semantics later. For example:

```{.k .exclude}
syntax Id ::= "main" [token]
```

Here, we declare `main` as a token of sort `Id`. Instead of being parsed as a 
symbol, it gets parsed as a token, generating a typed string in the AST.
This can be useful in a semantics of C because the parser typically doesn't 
handle the `main` function in any special way; it's only the semantics that 
gives it special treatment.

The syntax of integers in C has a more complex lexical structure than the one
of built-in integers in K, and a production defining them could look as 
follows:

```{.k .exclude}
syntax IntConstant ::= r"(([1-9][0-9]*)|(0[0-7]*)|(0[xX][0-9a-fA-F]+))(([uU][lL]?)|([uU]((ll)|(LL)))|([lL][uU]?)|(((ll)|(LL))[uU]?))?" [token]
```

This is a long and complex regular expression, hard to read. In addition,
unlike a grammar, it is not particularly modular. However, we can get around 
this restriction by declaring _explicit_ regular expressions, giving them a 
name, and referring to them in productions.

Consider the following (equivalent) way to define the lexical syntax of
integers in C:

```{.k .exclude}
syntax IntConstant ::= r"({DecConstant}|{OctConstant}|{HexConstant})({IntSuffix}?)" [token]
syntax lexical DecConstant = r"{NonzeroDigit}({Digit}*)"
syntax lexical OctConstant = r"0({OctDigit}*)"
syntax lexical HexConstant = r"{HexPrefix}({HexDigit}+)"
syntax lexical HexPrefix = r"0x|0X"
syntax lexical NonzeroDigit = r"[1-9]"
syntax lexical Digit = r"[0-9]"
syntax lexical OctDigit = r"[0-7]"
syntax lexical HexDigit = r"[0-9a-fA-F]"
syntax lexical IntSuffix = r"{UnsignedSuffix}({LongSuffix}?)|{UnsignedSuffix}{LongLongSuffix}|{LongSuffix}({UnsignedSuffix}?)|{LongLongSuffix}({UnsignedSuffix}?)"
syntax lexical UnsignedSuffix = r"[uU]"
syntax lexical LongSuffix = r"[lL]"
syntax lexical LongLongSuffix = r"ll|LL"
```

As you can see, this is rather more verbose, but it has the benefit of being 
easier to read and understand, as well as providing increased modularity.

Note that we refer to a named regular expression by putting the name in curly
brackets. Note also that only the first sentence actually declares a new piece
of syntax in the language. `syntax lexical` only declares an explicit regular 
expression. 

Finally, recall that K uses [Flex](https://github.com/westes/flex) to implement 
its lexical analysis. As such, you can refer to the
[Flex Manual | Patterns](http://westes.github.io/flex/manual/Patterns.html#Patterns)
for a detailed description of the regular expression syntax supported. For
performance reasons, Flex's regular expressions are actually a regular 
language, and thus lack some of the syntactic convenience of modern "regular 
expression" libraries. If you need features that are not part of the syntax of 
Flex regular expressions, you are encouraged to express them via a grammar 
instead.

## Ahead-of-time parser generation

So far we have been entirely focused on K's support for just-in-time parsing,
where the parser is generated on the fly prior to being used. This method 
offers faster parser generation, but its performance suffers if you have to 
repeatedly parse strings with the same parser. For this reason, when parsing
programs, it is generally recommended to use K's ahead-of-time parser 
generation based on [GNU Bison](https://www.gnu.org/software/bison/).

You can enable ahead-of-time parsing via the `--gen-bison-parser` flag to 
`kompile`. This will make use of Bison's 
[LR(1) parser](https://en.wikipedia.org/wiki/Canonical_LR_parser) generator. As
such, if your grammar is not LR(1), it may not parse exactly the same as if
you were to use the just-in-time parser because Bison will automatically pick
one of the possible branches whenever it encounters a shift-reduce or
reduce-reduce conflict. In this case, you can either modify your grammar to be
LR(1), or you can use Bison's GLR support by passing flag
`--gen-glr-bison-parser` to `kompile` instead. Note that if your grammar is ambiguous,
the ahead-of-time parser will not provide you with particularly readable error
messages at this time.

`kompile --gen-bison-parser 'lesson-03-a.k'` gives

```
[Warning] Compiler: Could not find main syntax module with name
LESSON-03-A-SYNTAX in definition.  Use --syntax-module to specify one. Using
LESSON-03-A as default.
[Warning] Inner Parser: Skipping modules [ML-SYNTAX] tagged as not-lr1 which
are not supported by Bison.
```

We have seen the first warning before, and we discussed it in
[Lesson 1.2](../02_basics/README.md). The second warning we get is a side 
effect of the first one, informing that certain modules&mdash;e.g., for 
parsing&mdash;were excluded from the grammar generation because they were 
known to cause Bison to crash or behave incorrectly.

Next, run

`lesson-03-a-kompiled/parser_PGM and-or.bool`

to see that now you don't get an error when parsing. Even though our grammar
is ambiguous, the LR(1) algorithm generates a single parse tree. The output, 
minus formatting, is the following:

```
inj{SortBoolean{}, SortKItem{}}(
  Lbl'UndsAnd-And-UndsUnds'LESSON-03-A'Unds'Boolean'Unds'Boolean'Unds'Boolean{}(
    Lbltrue'Unds'LESSON-03-A'Unds'Boolean{}(),
    Lbl'UndsPipePipeUndsUnds'LESSON-03-A'Unds'Boolean'Unds'Boolean'Unds'Boolean{}(
      Lblfalse'Unds'LESSON-03-A'Unds'Boolean{}(),
      Lblfalse'Unds'LESSON-03-A'Unds'Boolean{}()
    )
  )
)
```

At closer look, you see it is the AST where `||` has higher priority (Fig. 3-B).

Compare this with the output given when running the same command, but when the
ahead-of-time parser has been enabled with flag `--gen-glr-bison-parser`:

```
inj{SortBoolean{}, SortKItem{}}(
  Lblamb{SortBoolean{}}(
    Lbl'UndsAnd-And-UndsUnds'LESSON-03-A'Unds'Boolean'Unds'Boolean'Unds'Boolean{}(
      Lbltrue'Unds'LESSON-03-A'Unds'Boolean{}(),
      Lbl'UndsPipePipeUndsUnds'LESSON-03-A'Unds'Boolean'Unds'Boolean'Unds'Boolean{}(
        Lblfalse'Unds'LESSON-03-A'Unds'Boolean{}(),
        Lblfalse'Unds'LESSON-03-A'Unds'Boolean{}()
      )
    ),
    Lbl'UndsPipePipeUndsUnds'LESSON-03-A'Unds'Boolean'Unds'Boolean'Unds'Boolean{}(
      Lbl'UndsAnd-And-UndsUnds'LESSON-03-A'Unds'Boolean'Unds'Boolean'Unds'Boolean{}(
        Lbltrue'Unds'LESSON-03-A'Unds'Boolean{}(),
        Lblfalse'Unds'LESSON-03-A'Unds'Boolean{}()
      ),
      Lblfalse'Unds'LESSON-03-A'Unds'Boolean{}()
    )
  )
)
```

In this case, we get both ASTs. Since our grammar is ambiguous, the GLR 
algorithm produces the complete parse forest. The ambiguity is indicated in the
above KORE output by node `Lblamb` and its two children, each a possible AST of
the term `true && false || false`.

Finally, note that, for a K definition named `foo.k`, and directory 
`foo-kompiled` created when running `kompile`, you can invoke the ahead-of-time
parser you generated by executing `foo-kompiled/parser_PGM <file>` on a file.

## Exercises

1. Compile `lesson-03-d.k` with ahead-of-time parsing enabled. Then compare
how long it takes to run `kast --output kore and-or-left.bool` with how long it
takes to run `lesson-03-d-kompiled/parser_PGM and-or-left.bool`. Confirm for
yourself that both produce the same result, but that the latter is faster.

2. Define a simple grammar consisting of integers, brackets, addition,
subtraction, multiplication, division, and unary negation. Integers should be
in decimal form and lexically without a sign, whereas negative numbers can be
represented via unary negation. Ensure that you are able to parse some basic
arithmetic expressions using a generated ahead-of-time parser. Do not worry
about disambiguating the grammar or about writing rules to implement the
operations in this definition.

3. Write a program where the meaning of the arithmetic expression based on
the grammar you defined above is ambiguous, and then write programs that
express each individual intended meaning using brackets.

## Next lesson

Once you have completed the exercises above, you can continue to
[Lesson 1.4: Disambiguating Parses](../04_disambiguation/README.md).
