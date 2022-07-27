# Lesson 1.5: Modules, Imports, and Requires

The purpose of this lesson is to explain how K definitions can be broken into
separate modules and files and how these distinct components combine into a
complete K definition.

## K's outer syntax

Recall from [Lesson 1.3](../03_parsing/README.md) that K's grammar is broken
into two components: the **outer syntax** of K and the **inner syntax** of K.
Outer syntax, as previously mentioned, consists of **requires**, **modules**,
**imports**, and **sentences**. A K semantics is expressed by the set of
sentences contained in the definition. The scope of what is considered
contained in that definition is determined both by the **main semantics
module** of a K definition, as well as the **requires** and **imports** present
in the file that contains that module.

## Basic module syntax

The basic unit of grouping sentences in K is the module. A module consists
of a **module name**, an optional list of **attributes**, a list of
**imports**, and a list of **sentences**.

A module name consists of one or more groups of letters, numbers, or
underscores, separated by a hyphen. Here are some valid module names: `FOO`,
`FOO-BAR`, `foo0`, `foo0_bar-Baz9`. Here are some invalid module names: `-`,
`-FOO`, `BAR-`, `FOO--BAR`. Stylistically, modules names are usually all
uppercase with hyphens separating words, but this is not strictly enforced.

Some example modules include an empty module:

```k
module LESSON-05-A

endmodule
```

A module with some attributes:

```k
module LESSON-05-B [attr1, attr2, attr3(value)]

endmodule
```

A module with some sentences:

```k
module LESSON-05-C
  syntax Boolean ::= "true" | "false"
  syntax Boolean ::= "not" Boolean [function]
  rule not true => false
  rule not false => true
endmodule
```

## Imports

Thus far we have only discussed definitions containing a single module. 
Definitions can also contain multiple modules, in which one module imports
others.

An import in K appears at the top of a module, prior to any sentences. It can
be specified with the `imports` keyword, followed by a module name.

For example, here is a simple definition with two modules (`lesson-05-d.k`):

```k
module LESSON-05-D-1
  syntax Boolean ::= "true" | "false"
  syntax Boolean ::= "not" Boolean [function]
endmodule

module LESSON-05-D
  imports LESSON-05-D-1

  rule not true => false
  rule not false => true
endmodule
```

This K definition is equivalent to the definition expressed by the single module
`LESSON-05-C`. Essentially, by importing a module, we include all of the
sentences in the module being imported into the module that we import from.
There are a few minor differences between importing a module and simply
including its sentences in another module directly, but we will cover these
differences later. Essentially, you can think of modules as a way of
conceptually grouping sentences in a larger K definition.

### Exercise

Modify `lesson-05-d.k` to include four modules: one containing the syntax, two
with one rule each that imports the first module, and a final module
`LESSON-05-D` containing no sentences that imports the second and third module.
Check to make sure the definition still compiles and that you can still evaluate
the `not` function.

## Parsing in the presence of multiple modules

As you may have noticed, each module in a definition can express a distinct set
of syntax. When parsing the sentences in a module, we use the syntax
**of that module**, enriched with the basic syntax of K, in order to parse
rules in that module. For example, the following definition is a parser error
(`lesson-05-e.k`):

```{.k .error}
module LESSON-05-E-1
  rule not true => false
  rule not false => true
endmodule

module LESSON-05-E-2
  syntax Boolean ::= "true" | "false"
  syntax Boolean ::= "not" Boolean [function]
endmodule
```

This is because the syntax referenced in module `LESSON-05-E-1`, namely, `not`,
`true`, and `false`, is not imported by that module. You can solve this problem
 by simply importing the modules containing the syntax you want to use in your
sentences.

## Main syntax and semantics modules

When we are compiling a K definition, we need to know where to start. We
designate two specific **entry point modules**: the **main syntax module**
and the **main semantics module**. The main syntax module, as well as all the
modules it imports recursively, are used to create the parser for programs that
you use to parse programs that you execute with `krun`. The main semantics
module, as well as all the modules it imports recursively, are used to
determine the rules that can be applied at runtime in order to execute a
program. For example, in the above example, if the main semantics module is
module `LESSON-05-D-1`, then `not` is an uninterpreted function (i.e., has no
rules associated with it), and the rules in module `LESSON-05-D-2` are not
included.

While you can specify the entry point modules explicitly by passing the
`--main-module` and `--syntax-module` flags to `kompile`, by default, if you
type `kompile foo.k`, then the main semantics module will be `FOO` and the
main syntax module will be `FOO-SYNTAX`.

## Splitting a definition into multiple files

So far, while we have discussed ways to break definitions into separate
conceptual components (modules), K also provides a mechanism for combining
multiple files into a single K definition, namely, the **requires** directive.

In K, the `requires` keyword has two meanings. The first, the **requires**
statement, appears at the top of a K file, prior to any module declarations. It
consists of the keyword `requires` followed by a double-quoted string. The
second meaning of the `requires` keyword will be covered in a later lesson,
but it is distinguished because the second case occurs only inside modules.

The string passed to the **requires** statement contains a filename. When you run
`kompile` on a file, it will look at all of the `requires` statements in that
file, look up those files on disk, parse them, and then recursively process all
the **requires** statements in those files. It then combines all the modules in all
of those files together, and uses them collectively as the set of modules to
which `imports` statements can refer.

## Putting it all together

Putting it all together, here is one possible way in which we could break the
definition `lesson-02-c.k` from [Lesson 1.2](../02_basics/README.md) into
multiple files and modules:

`colors.k`:

```k
module COLORS
  syntax Color ::= Yellow()
                 | Blue()
endmodule
```

`fruits.k`:

```k
module FRUITS
  syntax Fruit ::= Banana()
                 | Blueberry()
endmodule
```

`colorOf.k`:

```{.k .exclude}
requires "fruits.k"
requires "colors.k"

module COLOROF-SYNTAX
  imports COLORS
  imports FRUITS

  syntax Color ::= colorOf(Fruit) [function]
endmodule

module COLOROF
  imports COLOROF-SYNTAX

  rule colorOf(Banana()) => Yellow()
  rule colorOf(Blueberry()) => Blue()
endmodule
```

You would then compile this definition with `kompile colorOf.k` and use it the
same way as the original, single-module definition.

### Exercise

Modify the name of the `COLOROF` module, and then recompile the definition.
Try to understand why you now get a compiler error. Then, resolve this compiler
error by passing the `--main-module` and `--syntax-module` flags to kompile.

## Include path

One note can be made about how paths are resolved in `requires` statements.

By default, the path you specify is allowed to be an absolute or a relative
path. If the path is absolute, that exact file is imported. If the path is
relative, a matching file is looked for within all of the 
**include directories** specified to the compiler. By default, the include
directories include the current working directory, followed by the
`include/kframework/builtin` directory within your installation of K. You can
also pass one or more directories to `kompile` via the `-I` command line flag,
in which case these directories are prepended to the beginning of the list.

## Exercises

1. Take the solution to lesson 1.4, problem 2 which included the explicit
priority and associativity declarations, and modify the definition so that
the syntax of integers and brackets is in one module, the syntax of addition,
subtraction, and unary negation is in another module, and the syntax of
multiplication and division is in a third module. Make sure you can still parse
the same set of expressions as before. Place priority declarations in the main
module.

2. Modify `lesson-02-d.k` from lesson 1.2 so that the rules and syntax are in
separate modules in separate files.

3. Place the file containing the syntax from problem 2 in another directory,
then recompile the definition. Observe why a compilation error occurs. Then
fix the compiler error by passing `-I` to kompile.

## Next lesson

Once you have completed the above exercises, you can continue to
[Lesson 1.6: Integers and Booleans](../06_ints_and_bools/README.md).
