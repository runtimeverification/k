# Lesson 1.8: Literate Programming with Markdown

The purpose of this lesson is to teach a paradigm for performing literate
programming in K, and explain how this can be used to create K definitions
that are also documentation.

## Markdown and K

The K tutorial so far has been written in
[Markdown](https://guides.github.com/features/mastering-markdown/). Markdown, 
for those not already familiar, is a lightweight plain-text format for styling
text. From this point onward, we assume you are familiar with Markdown and how
to write Markdown code. You can refer to the above link for a tutorial if you
are not already familiar.

What you may not necessarily realize, however, is that the K tutorial is also
a sequence of K definitions written in the manner of
[Literate Programming](https://en.wikipedia.org/wiki/Literate_programming).
For detailed information about Literate Programming, you can read the linked
Wikipedia article, but the short summary is that literate programming is a way
of intertwining documentation and code together in a manner that allows
executable code to also be, simultaneously, a documented description of that
code.

K is provided with built-in support for literate programming using Markdown.
By default, if you pass a file with the `.md` file extension to `kompile`, it
will look for any code blocks containing k code in that file, extract out
that K code into pure K, and then compile it as if it were a `.k` file.

A K code block begins with a line of text containing the keyword ` ```k `,
and ends when it encounters another ` ``` ` keyword.

For example, if you view the markdown source of this document, this is a K
code block:

```k
module LESSON-08
  imports INT
```

Only the code inside K code blocks will actually be sent to the compiler. The
rest, while it may appear in the document when rendered by a markdown viewer,
is essentially a form of code comment.

When you have multiple K code blocks in a document, K will append each one
together into a single file before passing it off to the outer parser.

For example, the following code block contains sentences that are part of the
`LESSON-08` module that we declared the beginning of above:

```k
  syntax Int ::= Int "+" Int [function]
  rule I1 + I2 => I1 +Int I2
```

### Exercise

Compile this file with `kompile README.md --main-module LESSON-08`. Confirm
that you can use the resulting compiled definition to evaluate the `+`
function.

## Markdown Selectors

On occasion, you may want to generate multiple K definitions from a single
Markdown file. You may also wish to include a block of syntax-highlighted K
code that nonetheless does **not** appear as part of your K definition. It is
possible to accomplish this by means of the built-in support for syntax
highlighting in Markdown. Markdown allows a code block that was begun with
` ``` ` to be immediately followed by a string which is used to signify what
programming language the following code is written in. However, this feature
actually allows arbitrary text to appear describing that code block. Markdown
parsers are able to parse this text and render the code block differently
depending on what text appears after the backticks.

In K, you can use this functionality to specify one or more
**Markdown selectors** which are used to describe the code block. A Markdown
selector consists of a sequence of characters containing letters, numbers, and
underscores. A code block can be designated with a single selector by appending
the selector immediately following the backticks that open the code block.

For example, here is a code block with the `foo` selector:

```foo
foo bar
```

Note that this is not K code. By convention, K code should have the `k`
selector on it. You can express multiple selectors on a code block by putting
them between curly braces and prepending each with the `.` character. For
example, here is a code block with the `foo` and `k` selectors:

```{.k .foo}
  syntax Int ::= foo(Int) [function]
  rule foo(0) => 0
```

Because this code block contains the `k` Markdown selector, by default it is
included as part of the K definition being compiled.

### Exercise

Confirm this fact by using `krun` to evaluate `foo(0)`.

## Markdown Selector Expressions

By default, as previously stated, K includes in the definition any code block
with the `k` selector. However, this is merely a specific instance of a general
principle, namely, that K allows you to control which selectors get included
in your K definition. This is done by means of the `--md-selector` flag to
`kompile`. This flag accepts a **Markdown selector expression**, which you
can essentially think of as a kind of boolean algebra over Markdown selectors.
Each selector becomes an atom, and you can combine these atoms via the `&`, 
`|`, `!`, and `()` operators.

Here is a grammar, written in K, of the language of Markdown selector
expressions:

```{.k .selector}
  syntax Selector ::= r"[0-9a-zA-Z_]+" [token]
  syntax SelectorExp ::= Selector
                       | "(" SelectorExp ")" [bracket]
                       > right:
                         "!" SelectorExp
                       > right:
                         SelectorExp "&" SelectorExp
                       > right:
                         SelectorExp "|" SelectorExp
```

Here is a selector expression that selects all the K code blocks in this
definition except the one immediately above:

```
k & (! selector)
```

## Addendum

This code block exists in order to make the above lesson a syntactically valid
K definition. Consider why it is necessary.

```k
endmodule
```

### Exercises

1. Compile this lesson with the selector expression `k & (! foo)` and confirm
that you get a parser error if you try to evaluate the `foo` function with the
resulting definition.

2. Compile [Lesson 3](../03_parsing/README.md) as a K definition. Identify
why it fails to compile. Then pass an appropriate `--md-selector` to the
compiler in order to make it compile.

3. Modify your calculator application from lesson 7, problem 2, to be written
in a literate style. Consider what text might be appropriate to turn the
resulting markdown file into documentation for your calculator.
