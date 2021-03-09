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
defines a relatively basic calculator capable of evaluating boolean expressions
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
exclusively on the first mechinism, where the `::=` symbol is followed by an
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
parsed and interpreted by K's interpreter. Seen this way, you can see how that
string represents a sentence in the formal language defined by the above
grammar. K then parses it automatically into an AST of that term, and then,
since the symbol `colorOf` is a function, it evaluates that function using
the rules that define it.

Bringing us back to the file `lesson-03-a.k`, we can see that this grammar
has given a simple BNF grammar for expressions over booleans. We have defined
constructors corresponding to the boolean values true and false, and functions
corresponding to the boolean operators for and, or, not, and xor. We have also
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
run (from the same  directory):

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
`And` in there. This is `KORE`, the intermediate representation of K, and we
will cover it in detail later.

## Disambiguation

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

Essentially what this error is saying is, `kast` was unable to parse this
program because it is ambiguous. K's just-in-time parser is what is technically
known as a GLL parser, which in practice means it handles the full generality
of context-free grammars, including those grammars which are ambiguous. An
ambiguous grammar is one where one or more sentences in the grammar might be
able to be parsed into more than one distinct AST. In this example, it can't
decide whether it should be parsed as `(true && false) || false` or as
`true && (false || false)`. As a result, it reports the error to the user.

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
unique AST with no error. If you look, you may spot that the bracket itself
does not appear in the AST. In fact, this is a property unique to brackets:
productions with the bracket attribute are not represented in the parsed AST
of a term, and the child of the bracket is folded immediately into the parent
term. This is the reason for the requirement that a bracket production have
a single non-terminal of the same sort as the production itself.

## Priority blocks

Of course, in practice, very few formal languages outside the domain of
natural language processing are ambiguous. The main reason for this is that
parsing unambiguous languages is asymptotically faster than parsing ambiguous
languages. Programming language designers instead prefer to use a notion of
operator precedence and associativity to make expression grammars unambiguous
by automatically choosing certain parses over other parses in cases where the
grammar would otherwise be ambiguous.

While it is sometimes possible to explicitly rewrite the grammar to remove
these parses, because K's grammar specification and AST generation are
inextricably linked, this is generally discouraged. Instead, we use the
approach of explicitly expressing the relative precedence of different
operators in different situations in order to resolve the ambiguity.

For example, in C, `&&` binds tighter in precedence than `||`, meaning that
the expression `true && false || false` would be parsed as
`(true && false) || false`.

Consider, then, the third iteration on the grammar of this definition
(`lesson-03-e.k`):

```k
module LESSON-03-E

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
**less-than** operator describing a transitive partial ordering on the 
productions in the production block, expressing their relative priority.

To see this more concretely, let's look again at the program
`true && false || false`. As noted before, previously this program was
ambiguous because it was ambiguous whether the `&&` was a child of the `||`
or vice versa. However, because of the rule that a symbol with lesser priority
cannot appear as the direct child of a symbol with greater priority, and
because we can see from the above grammar that `&&` has a greater priority than
`||`, we **reject** the parse where `||` is under the `&&` operator. As a
result, we are left with the unambiguous parse `(true && false) || false`.
Similarly, `true || false && false` parses unambiguously as
`true || (false && false)`. Conversely, if the user explicitly wants the other
parse, they can express this parse using brackets. In other words, they can
explicitly write the program `true && (false || false)`. This still parses
successfully because the `||` operator is no longer the **direct** child of the
`&&` operator, but is instead the direct child of the `()` operator, and the
`&&` operator is an **indirect** parent. Indirect parents are completely
ignored when disambiguating; only the direct parent/child relation matters.

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
the sole non-terminal is both preceded by and followed by a terminal. As a
result, the priority rule is not applied when `()` is the parent. Because of
this, the program we mentioned above successfully parses.

## Associativity

Even having broken the expression grammar into priority blocks, the resulting
grammar is still ambiguous. We can see this if we try to parse the following
program (`assoc.bool`):

```
true && false && false
```

Priority blocks will not help us here: the problem comes between two parses
where both possible parses have a direct parent and child which is within a
single priority block.

This is where the notion of associativity comes into play. Essentially,
associativity applies the following additional rule to parses: a
left-associative symbol cannot appear as a direct rightmost child of a symbol
with equal priority; a right-associative symbol cannot appear as a direct
leftmost child of a symbol with equal priority; and a non-associative symbol
cannot appear as a direct leftmost **or** rightmost child of a symbol with
equal priority.

In C, binary operators are all left-associative, meaning that the expression 
`true && false && false` parses unambiguously as `(true && false) && false`,
because `&&` cannot appear as the rightmost child of itself.

Consider, then, the fourth iteration on the grammar of this definition
(`lesson-03-f.k`):

```k
module LESSON-03-F

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

For example, consider the following, different grammar (`lesson-03-g.k`):

```k
module LESSON-03-G

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

## Explicit priority and associativity declarations

Previously we have only considered the case where all of the productions
which you wish to express a priority or associativity relation over are
co-located in the same block of productions. However, in practice this is not
always feasible or desirable, especially as a definition grows in size across
multiple modules.

As a result of this, K provides a second way of declaring priority and
associativity relations.

Consider the following grammar, which we will name `lesson-03-h.k` and which
will express the exact same grammar relation as `lesson-03-f.k`

```k
module LESSON-03-H

  syntax Boolean ::= "true" [literal] | "false" [literal]
  syntax Boolean ::= "(" Boolean ")" [atom, bracket]
  syntax Boolean ::= "!" Boolean [not, function]
  syntax Boolean ::= Boolean "&&" Boolean [and, function]
  syntax Boolean ::= Boolean "^" Boolean [xor, function]
  syntax Boolean ::= Boolean "|" Boolean [or, function]

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

Sometimes priority and associativity proves insufficient to disambiguate a
grammar. In particular, sometimes it is desirable to be able to choose between
two ambiguous parses directly while still not rejecting any parses if the term
parsed is unambiguous. A good example of this is the famous "dangling else"
problem in imperative C-like languages.

Consider the following definition (`lesson-03-i.k`):

```k
module LESSON-03-I

  syntax Exp ::= "true" | "false"
  syntax Stmt ::= "if" "(" Exp ")" Stmt
                | "if" "(" Exp ")" Stmt "else" Stmt
                | ";"
endmodule
```

We can write the following program (`dangling-else.if`):

```
if (true) if (false) ; else ;
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

`if(_)__LESSON-03-I_Stmt_Exp_Stmt`(`true_LESSON-03-I_Exp`(.KList),`if(_)_else__LESSON-03-I_Stmt_Exp_Stmt_Stmt`(`false_LESSON-03-I_Exp`(.KList),`;_LESSON-03-I_Stmt`(.KList),`;_LESSON-03-I_Stmt`(.KList)))
2: syntax Stmt ::= "if" "(" Exp ")" Stmt "else" Stmt

`if(_)_else__LESSON-03-I_Stmt_Exp_Stmt_Stmt`(`true_LESSON-03-I_Exp`(.KList),`if(_)__LESSON-03-I_Stmt_Exp_Stmt`(`false_LESSON-03-I_Exp`(.KList),`;_LESSON-03-I_Stmt`(.KList)),`;_LESSON-03-I_Stmt`(.KList))
        Source(./dangling-else.if)
        Location(1,1,1,30)
```

Roughly, we see that the ambiguity is between an `if` with an `else` or an `if`
without an `else`. Siknce we want to pick the first parse, we can tell K to
"avoid" the second parse with the `avoid` attribute. Consider the following
modified definition (`lesson-03-j.k`):

```k
module LESSON-03-I

  syntax Exp ::= "true" | "false"
  syntax Stmt ::= "if" "(" Exp ")" Stmt
                | "if" "(" Exp ")" Stmt "else" Stmt [avoid]
                | ";"
endmodule
```

Here we have added the `avoid` attribute to the `else` production. As a result,
when an ambiguity occurs and one or more of the possible parses has that symbol
at the top of the ambiguous part of the parse, we remove those parses from
consideration and consider only those remaining. The `prefer` attribute behaves
similarly, but instead removes all parses which do not have that attribute.
In both cases, no action is taken if the parse is not ambiguous.

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

For example, we might define the integer token in C with the following
production:

```k
syntax IntConstant ::= r"(([1-9][0-9]*)|(0[0-7]*)|(0[xX][0-9a-fA-F]+))(([uU][lL]?)|([uU]((ll)|(LL)))|([lL][uU]?)|(((ll)|(LL))[uU]?))?" [token]
```

As you can see, the main difference with this production is the `r` preceding
the terminal and the `token` attribute. The `r` indicates that what follows
is a regular expression. It is also possible to define tokens that do not
use regular expressions. This can be useful when you wish to declare particular
identifiers for use in your semantics later. For example:

```k
syntax Id ::= "main" [token]
```

Here we declare that `main` is a token of sort `Id`. Instead of being parsed
as a symbol, it gets parsed as a token instead, generating a typed string
in the AST. This is useful because the parser generally does not treat the
`main` function in C specially; only the semantics treats it specially.

As you may have noted above, however, long and complex regular expressions
can be hard to read. They also suffer from the problem that unlike a grammar,
they are not particularly modular.

We can get around this restriction by declaring explicit regular expressions,
giving them a name, and then referring to them in productions.

Consider the following (equivalent) way to define the lexical syntax of
integers in C:

```k
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

Finally, so far we have been entirely focused on K's support for just-in-time
parsing, where the parser is generated on the fly prior to being used.
This benefits from being faster to generate the parser, but it suffers in
performance if you have to repeatedly parse strings with the same parser.
For this reason, it is generally encouraged that when parsing programs,
you use K's ahead-of-time parser generation instead. K makes use of
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

1. Define a simple grammar consisting of integers, brackets, addition,
subtraction, multiplication, division, and unary negation. Integers should be
in decimal form and lexically without a sign, unary negation should bind
tighter than multiplication and division, which should bind tighter than
addition and subtraction, and each binary operator should be left associative.
Ensure that you are able to parse some basic arithmetic expressions using a
generated ahead-of-time parser. Do not worry about writing rules to implement
the operations in this definition.

2. Write a simple grammar containing at least one ambiguity that cannot be
resolved via priority or associativity, and then use the `prefer` attribute to
resolve that ambiguity.
