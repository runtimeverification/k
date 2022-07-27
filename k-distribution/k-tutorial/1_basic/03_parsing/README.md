# Lesson 1.3: BNF Syntax and Parser Generation

The purpose of this lesson is to explain the full syntax and semantics of
**productions** in K as well as how productions and other syntactic 
**sentences** can be used to define grammars for use parsing both rules as well
as programs.

## K's approach to parsing

K's grammar is divided into two components: the **outer syntax** of K and the
**inner syntax** of K.  Outer syntax refers to the parsing of **requires**,
**modules**, **imports**, and **sentences** in a K definition. Inner syntax
refers to the parsing of **rules** and **programs**. Unlike the outer syntax of
K, which is predetermined, much of the inner syntax of K is defined by you, the
developer. When rules or programs are parsed, they are parsed within the
context of a module. Rules are parsed in the context of the module in which
they exist, whereas programs are parsed in the context of the
**main syntax module** of a K definition. The productions and other syntactic
sentences in a module are used to construct the grammar of the module, which
is then used to perform parsing.

## Basic BNF productions

To illustrate how this works, we will consider a simple K definition which
defines a relatively basic calculator capable of evaluating Boolean expressions
containing and, or, not, and xor.

Input the following program into your editor as file `lesson-03-a.k`:

```k
module LESSON-03-A

  syntax Boolean ::= "true" | "false"
                   | "!" Boolean [function]
                   | Boolean "&&" Boolean [function]
                   | Boolean "^" Boolean [function]
                   | Boolean "||" Boolean [function]

endmodule
```

You will notice that the productions in this file look a little different than
the ones from the previous lesson. In point of fact, K has two different
mechanisms for defining productions. We have previously been focused
exclusively on the first mechanism, where the `::=` symbol is followed by an
alphanumeric identifier followed by a comma-separated list of sorts in
parentheses. However, this is merely a special case of a more generic mechanism
for defining the syntax of productions using a variant of
[BNF Form](https://en.wikipedia.org/wiki/Backus%E2%80%93Naur_form).

For example, in the previous lesson, we had the following set of productions:

```k
module LESSON-03-B
  syntax Color ::= Yellow() | Blue()
  syntax Fruit ::= Banana() | Blueberry()
  syntax Color ::= colorOf(Fruit) [function]
endmodule
```

It turns out that this is equivalent to the following definition which defines
the same grammar, but using BNF notation:

```k
module LESSON-03-C
  syntax Color ::= "Yellow" "(" ")" | "Blue" "(" ")"
  syntax Fruit ::= "Banana" "(" ")" | "Blueberrry" "(" ")"
  syntax Color ::= "colorOf" "(" Fruit ")" [function]
endmodule
```

In this example, the sorts of the argument to the function are unchanged, but
everything else has been wrapped in double quotation marks. This is because
in BNF notation, we distinguish between two types of **production items**:
**terminals** and **non-terminals**. A terminal represents simply a literal
string of characters that is verbatim part of the syntax of that production.
A non-terminal, conversely, represents a sort name, where the syntax of that
production accepts any valid term of that sort at that position.

This is why, when we wrote the program `colorOf(Banana())`, `krun` was able to
execute that program: because it represented a term of sort `Color` that was
parsed and interpreted by K's interpreter. In other words, `krun` parses and
interprets terms according to the grammar defined by the developer. It is
automatically converted into an AST of that term, and then the `colorOf`
function is evaluated using the function rules provided in the definition.

Bringing us back to the file `lesson-03-a.k`, we can see that this grammar
has given a simple BNF grammar for expressions over Booleans. We have defined
constructors corresponding to the Boolean values true and false, and functions
corresponding to the Boolean operators for and, or, not, and xor. We have also
given a syntax for each of these functions based on their syntax in the `C`
programming language. As such, we can now write programs in the simple language
we have defined.

Input the following program into your editor as `and.bool` in the same
directory:

```
true && false
```

We cannot interpret this program yet, because we have not given rules defining
the meaning of the `&&` function yet, but we can parse it. To do this, you can
run (from the same directory):

```
kast --output kore and.bool
```

`kast` is K's just-in-time parser. It will generate a grammar from your K
definition on the fly and use it to parse the program passed on the command
line. The `--output` flag controls how the resulting AST is represented; don't
worry about the possible values yet, just use `kore`.

You ought to get the following AST printed on standard output, minus the
formatting:

```
inj{SortBoolean{}, SortKItem{}}(
  Lbl'UndsAnd-And-UndsUnds'LESSON-03-A'Unds'Boolean'Unds'Boolean'Unds'Boolean{}(
    Lbltrue'Unds'LESSON-03-A'Unds'Boolean{}(),
    Lblfalse'Unds'LESSON-03-A'Unds'Boolean{}()
  )
)
```

Don't worry about what exactly this means yet, just understand that it
represents the AST of the program that you just parsed. You ought to be able
to recognize the basic shape of it by seeing the words `true`, `false`, and
`And` in there. This is **Kore**, the intermediate representation of K, and we
will cover it in detail later.

Note that you can also tell `kast` to print the AST in other formats. For a
more direct representation of the original K, while still maintaining the
structure of an AST, you can say `kast --output kast and.bool`. This will
yield the following output:

```
`_&&__LESSON-03-A_Boolean_Boolean_Boolean`(
  `true_LESSON-03-A_Boolean`(.KList),
  `false_LESSON-03-A_Boolean`(.KList)
)
```

Note how the first output is largely a name-mangled version of the second
output. The one difference is the presence of the `inj` symbol in the KORE
output. We will talk more about this in later lessons.

### Exercise

Parse the expression `false || true` with `--output kast`. See if you can
predict approximately what the corresponding output would be with
`--output kore`, then run the command yourself and compare it to your
prediction.

## Ambiguities

Now let's try a slightly more advanced example. Input the following program
into your editor as `and-or.bool`:

```
true && false || false
```

When you try and parse this program, you ought to see the following error:

```
[Error] Inner Parser: Parsing ambiguity.
1: syntax Boolean ::= Boolean "||" Boolean [function]

`_||__LESSON-03-A_Boolean_Boolean_Boolean`(`_&&__LESSON-03-A_Boolean_Boolean_Boolean`(`true_LESSON-03-A_Boolean`(.KList),`false_LESSON-03-A_Boolean`(.KList)),`false_LESSON-03-A_Boolean`(.KList))
2: syntax Boolean ::= Boolean "&&" Boolean [function]

`_&&__LESSON-03-A_Boolean_Boolean_Boolean`(`true_LESSON-03-A_Boolean`(.KList),`_||__LESSON-03-A_Boolean_Boolean_Boolean`(`false_LESSON-03-A_Boolean`(.KList),`false_LESSON-03-A_Boolean`(.KList)))
        Source(./and-or.bool)
        Location(1,1,1,23)
```

This error is saying that `kast` was unable to parse this program because it is
ambiguous. K's just-in-time parser is a GLL parser, which means it can handle
the full generality of context-free grammars, including those grammars which
are ambiguous. An ambiguous grammar is one where the same string can be parsed
as multiple distinct ASTs. In this example, it can't decide whether it should
be parsed as `(true && false) || false` or as `true && (false || false)`. As a
result, it reports the error to the user.

## Brackets

Currently there is no way of resolving this ambiguity, making it impossible
to write complex expressions in this language. This is obviously a problem.
The standard solution in most programming languages to this problem is to
use parentheses to indicate the appropriate grouping. K generalizes this notion
into a type of production called a **bracket**. A bracket production in K
is any production with the `bracket` attribute. It is required that such a
production only have a single non-terminal, and the sort of the production
must equal the sort of that non-terminal. However, K does not otherwise
impose restrictions on the grammar the user provides for a bracket. With that
being said, the most common type of bracket is one in which a non-terminal
is surrounded by terminals representing some type of bracket such as
`()`, `[]`, `{}`, `<>`, etc. For example, we can define the most common
type of bracket, the type used by the vast majority of programming languages,
quite simply.

Consider the following modified definition, which we will save to
`lesson-03-d.k`:

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

In this definition, if the user does not explicitly define parentheses, the
grammar remains ambiguous and K's just-in-time parser will report an error.
However, you are now able to parse more complex programs by means of explicitly
grouping subterms with the bracket we have just defined.

Consider `and-or-left.bool`:

```
(true && false) || false
```

Now consider `and-or-right.bool`:

```
true && (false || false)
```

If you parse these programs with `kast`, you will once again get a single
unique AST with no error. If you look, you might notice that the bracket itself
does not appear in the AST. In fact, this is a property unique to brackets:
productions with the bracket attribute are not represented in the parsed AST
of a term, and the child of the bracket is folded immediately into the parent
term. This is the reason for the requirement that a bracket production have
a single non-terminal of the same sort as the production itself.

### Exercise

Write out what you expect the AST to be arising from parsing these two programs
above with `--output kast`, then parse them yourself and compare them to the
AST you expected. Confirm for yourself that the bracket production does not
appear in the AST.

## Tokens

So far we have seen how we can define the grammar of a language. However,
the grammar is not the only relevant part of parsing a language. Also relevant
is the lexical syntax of the language. Thus far, we have implicitly been using
K's automatic lexer generation to generate a token in the scanner for each
terminal in our grammar. However, sometimes we wish to define more complex
lexical syntax. For example, consider the case of integers in C: an integer
consists of a decimal, octal, or hexadecimal number followed by an optional
suffix indicating the type of the literal.

In theory it would be possible to define this syntax via a grammar, but not
only would it be cumbersome and tedious, you would also then have to deal with
an AST generated for the literal which is not convenient to work with.

Instead of doing this, K allows you to define **token** productions, where
a production consists of a regular expression followed by the `token`
attribute, and the resulting AST consists of a typed string containing the
value recognized by the regular expression.

For example, the builtin integers in K are defined using the following
production:

```{.k .exclude}
syntax Int ::= r"[\\+-]?[0-9]+" [token]
```

Here we can see that we have defined that an integer is an optional sign
followed by a nonzero sequence of digits. The `r` preceding the terminal
indicates that what appears inside the double quotes is a regular expression,
and the `token` attribute indicates that terms which parse as this production
should be converted into a token by the parser.

It is also possible to define tokens that do not use regular expressions. This
can be useful when you wish to declare particular identifiers for use in your
semantics later. For example:

```{.k .exclude}
syntax Id ::= "main" [token]
```

Here, we declare that `main` is a token of sort `Id`. Instead of being parsed
as a symbol, it gets parsed as a token, generating a typed string in the AST.
This is useful in a semantics of C because the parser generally does not treat
the `main` function in C specially; only the semantics treats it specially.

Of course, languages can have more complex lexical syntax. For example, if we
wish to define the syntax of integers in C, we could use the following
production:

```{.k .exclude}
syntax IntConstant ::= r"(([1-9][0-9]*)|(0[0-7]*)|(0[xX][0-9a-fA-F]+))(([uU][lL]?)|([uU]((ll)|(LL)))|([lL][uU]?)|(((ll)|(LL))[uU]?))?" [token]
```

As you may have noted above, long and complex regular expressions
can be hard to read. They also suffer from the problem that unlike a grammar,
they are not particularly modular.

We can get around this restriction by declaring explicit regular expressions,
giving them a name, and then referring to them in productions.

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

As you can see, this is rather more verbose, but it has the benefit of both
being much easier to read and understand, and also increased modularity.
Note that we refer to a named regular expression by putting the name in curly
brackets. Note also that only the first sentence actually declares a new piece
of syntax in the language. When the user writes `syntax lexical`, they are only
declaring a regular expression. To declare an actual piece of syntax in the
grammar, you still must actually declare an explicit token production.

One final note: K uses [Flex](https://github.com/westes/flex) to implement
its lexical analysis. As a result, you can refer to the
[Flex Manual](http://westes.github.io/flex/manual/Patterns.html#Patterns)
for a detailed description of the regular expression syntax supported. Note
that for performance reasons, Flex's regular expressions are actually a regular
language, and thus lack some of the syntactic convenience of modern
"regular expression" libraries. If you need features that are not part of the
syntax of Flex regular expressions, you are encouraged to express them via
a grammar instead.

## Ahead-of-time parser generation

So far we have been entirely focused on K's support for just-in-time parsing,
where the parser is generated on the fly prior to being used. This benefits
from being faster to generate the parser, but it suffers in performance if you
have to repeatedly parse strings with the same parser. For this reason, it is
generally encouraged that when parsing programs, you use K's ahead-of-time
parser generation. K makes use of
[GNU Bison](https://www.gnu.org/software/bison/) to generate parsers.

By default, you can enable ahead-of-time parsing via the `--gen-bison-parser`
flag to `kompile`. This will make use of Bison's LR(1) parser generator. As
such, if your grammar is not LR(1), it may not parse exactly the same as if
you were to use the just-in-time parser, because Bison will automatically pick
one of the possible branches whenever it encounters a shift-reduce or
reduce-reduce conflict. In this case, you can either modify your grammar to be
LR(1), or you can enable use of Bison's GLR support by instead passing 
`--gen-glr-bison-parser` to `kompile`. Note that if your grammar is ambiguous,
the ahead-of-time parser will not provide you with particularly readable error
messages at this time.

If you have a K definition named `foo.k`, and it generates a directory when
you run `kompile` called `foo-kompiled`, you can invoke the ahead-of-time
parser you generated by running `foo-kompiled/parser_PGM <file>` on a file.

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

Once you have completed the above exercises, you can continue to
[Lesson 1.4: Disambiguating Parses](../04_disambiguation/README.md).
