# Lesson 1.20: K Backends and the Haskell Backend

The purpose of this lesson is to teach about the multiple backends of K,
in particular the Haskell Backend which is the complement of the backend we
have been using so far.

## K Backends

Thus far, we have not discussed the distinction between the K frontend and
the K backends at all. We have simply assumed that if you run `kompile` on a
K definition, there will be a compiler backend that will allow you to execute
the K definition you have compiled.

K actually has multiple different backends. The one we have been using so far
implicitly, the default backend, is called the **LLVM Backend**. It is
designed to support efficient, optimized concrete execution and search. It
does this by compiling your K definition to LLVM bitcode and then using LLVM
to generate machine code for it that is compiled and linked and executed.
However, K is a formal methods toolkit at the end of the day, and the primary
goal many people have when defining a programming language in K is to
ultimately be able to perform more advanced verification on programs in their
programming language.

It is for this purpose that K also provides the **Haskell Backend**, so called
because it is implemented in Haskell. While we will cover the features of the
Haskell Backend in more detail in the next two lessons, the important thing to
understand is that it is a separate backend which is optimized for more formal
reasoning about programming languages. While it is capable of performing
concrete execution, it does not do so as efficiently as the LLVM Backend.
In exchange, it provides more advanced features.

## Choosing a backend

You can choose which backend to use to compile a K definition by means of the
`--backend` flag to `kompile`. By default, if you do not specify this flag, it
is equivalent to if you had specified `--backend llvm`. However, to use the
Haskell Backend instead, you can simply say `kompile --backend haskell` on a
particular K definition.

As an example, here is a simple K definition that we have seen before in the
previous lesson (`lesson-20.k`):

```k
module LESSON-20
  imports INT

  rule I => I +Int 1
    requires I <Int 100
endmodule
```

Previously we compiled this definition using the LLVM Backend, but if we
instead execute the command `kompile lesson-20.k --backend haskell`, we
will get an interpreter for this K definition that is implemented in Haskell
instead. Unlike the default LLVM Backend, the Haskell Backend is not a
compiler per se. It does not generate new Haskell code corresponding to your
programming language and then compile and execute it. Instead, it is an
interpreter which reads the generated IR from `kompile` and implements in
Haskell an interpreter that is capable of interpreting any K definition.

### Exercise

Try running the program `0` in this K definition on the Haskell Backend and
compare the final configuration to what you would get compiling the same
definition with the LLVM Backend.

## Legacy backends

As a quick note, K does provide two other backends, which exist primarily
as legacy code which should be considered deprecated. These are the
**Java Backend** and the **OCAML Backend**. The Java Backend is essentially
a precursor to the Haskell Backend, and the OCAML Backend is essentially a
precursor to the LLVM Backend. We will not cover these backends in any detail
since they are deprecated, but we still mention them here for the purposes
of understanding.

## Exercises

1. Compile your solution to Lesson 1.18, Problem 2 with the Haskell Backend
and execute some programs. Compare the resulting configurations with the
output of the same program on the LLVM Backend.

## Next lesson

Once you have completed the above exercises, you can continue to
[Lesson 1.21: Unification and Symbolic Execution](../21_symbolic_execution/README.md).
