---
copyright: Copyright (c) Runtime Verification, Inc. All Rights Reserved.
---

# A Complete and Documented K Definition

In this lesson you will learn how to add formal comments to your K definition,
in order to nicely document it.  The generated document can be then used for
various purposes: to ease understanding the K definition, to publish it,
to send it to others, etc.

The K tool allows a literate programming style, where the executable
language definition can be documented by means of annotations. One such
annotation is the `latex(_)` annotation, where you can specify how to format
the given production when producing Latex output via the `--output latex`
option to `krun`, `kast`, and `kprove`.

There are three types of comments, which we discuss next.

## Ordinary comments

These use `//` or `/* ... */`, like in various programming languages.  These
comments are completely ignored.

## Document annotations

Use the `@` symbol right after `//` or `/*` in order for the comment to be
considered an annotation and thus be processed by the K tool when it
generates documentation.

As an example, we can go ahead and add such an annotation at the beginning
of the LAMBDA module, explaining how we define the syntax of this language.

## Header annotations

Use the `!` symbol right after `//` or `/*` if you want the comment to be
considered a header annotation, that is, one which goes before
`\begin{document}` in the generated Latex.  You typically need header
annotations to include macros, or to define a title, etc.

As an example, let us set a Latex length and then add a title and an
author to this K definition.

Compile the documentation and take a look at the results.  Notice the title.

Feel free to now add lots of annotations to `lambda.k`.

Then compile and check the result.  Depending on your PDF viewer, you
may also see a nice click-able table of contents, with all the sections
of your document.  This could be quite convenient when you define large
languages, because it helps you jump to any part of the semantics.

Tutorial 1 is now complete.  The next tutorial will take us through the
definition of a simple imperative language and will expose us to more
feature of the K framework and the K tool.

[MOVIE (out of date) [6'07"]](https://youtu.be/-pHgLqNMKac)
