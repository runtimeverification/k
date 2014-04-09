# K Tutorial
##### [Grigore Rosu](http://fsl.cs.illinois.edu/grosu) (<grosu@illinois.edu>)

In this tutorial you will learn how to use the K tool by means of a series of
lectures illustrating several simple languages defined using K.  Almost all the
material is presented in two forms: as ordinary text and a a short screencast movie.
We recommend the readers to either download the K tool from its URL
(<http://kframework.org>) and install it on their machines (K is implemented in Java,
so it is platform-independent) or use the provided online interface to execute the
tutorial lessons and do the proposed exercises.
The objective of this tutorial is twofold: to learn K (in folder
[tutorial/1_k](/tutorial/1_k/)) and to learn how to define languages across
various paradigms using K (in folder [tutorial/2_languages](/tutorial/2_languages/)).

It is recommended to study the languages defined in this folder in the
order indicated by their name, because K features already discussed in
a previous language definition will likely not be rediscussed in
latter definitions.

Below we discuss some of the high-level features of the K framework
and of the current K tool prototype, which you may find useful to know
about before starting to type and execute the tutorial examples.

Feel free to contact us at <info@kframework.org> for any questions or
concerns.

## K Framework Overview

[
[MOVIE (kframework.org) [9'59"]](http://fsl.cs.uiuc.edu/k-overview/k-overview_player.html)
|
[MOVIE (YouTube) [9'59"]](http://youtu.be/eSaIKHQOo4c)
|
[SLIDES (PPT)](http://www.kframework.org/images/e/e4/K-Overview.zip)
|
[SLIDES (PDF)](http://www.kframework.org/images/e/eb/K-Overview.pdf)
]

K is an executable semantic framework in which programming languages,
calculi, as well as type systems or formal analysis tools can be
defined by making use of configurations, computations and rules.
- Configurations organize the system/program state in units called
  cells, which are labeled and can be nested.
- Computations carry "computational meaning" as special nested list
  structures sequentializing computational tasks, such as fragments of
  program; in particular, computations extend the original language or
  calculus syntax.
- K (rewrite) rules generalize conventional rewrite rules by making it
  explicit which parts of the term they read-only, write-only, or do
  not care about.  This distinction makes K a suitable framework for
  defining truly concurrent languages or calculi even in the presence
  of sharing.

Since computations can be handled like any other terms in a rewriting
environment, that is, they can be matched, moved from one place to
another in the original term, modified, or even deleted, K is
particularly suitable for defining control-intensive language features
such as abrupt termination, exceptions, call/cc, concurrency, etc.


## The K Tool Prototype

The K tool prototype, called the "K tool" or the "K prototype" from
here on, is a prototype implementation of the K Framework written in
Java and Maude.  The K prototype is developed by a joint team of
faculty and students from the University of Illinois at
Urbana-Champaign, USA (the FSL group, led by professor Grigore Rosu),
the University Alexandru Ioan Cuza, Iasi, Romania (the FMSE group, led
by professor Dorel Lucanu), the University of Bucharest (professor
Traian Florin Serbanuta), as well as several individual enthusiasts.
A current list of the people involved in the project and their
specific roles can be accessed from <http://kframework.org>.

### Usage

Some of the languages defined so far using the K framework can be found in
the [tutorial/2_languages](/tutorial/2_languages/) directory, and many others
in the [samples](/samples/) directory.  For example, the directory

    tutorial/2_languages/1_simple/1_untyped

contains the definition of the untyped version of the SIMPLE language, while 

    tutorial/2_languages/1_simple/2_typed/1_static

contains the static semantics, i.e., the type checker.

We encourage you to contribute with examples to our distribution.
Please see the README file under [samples](/samples/) for instructions on how to do it.


### How It Works

We recommend the papers listed at <http://kframework.org> for a
deeper understanding of K.  Here we only discuss how our current K
tool works, reminding important facts about K in general by-need.

By default, the tool uses the syntax module of a definition to generate a
parser for that definition which can be used to parse programs and turn
them into their corresponding K-AST (KAST) format.  We briefly outline the
process below, using the untyped SIMPLE language
([tutorial/2_languages/1_simple/1_untyped](/tutorial/2_languages/1_simple/1_untyped)).


#### Parsing Programs

You may prefer to first define the syntax and then the semantics.
That is how most of the languages in the examples directory are
defined.  This reduces ambiguities in the parser and therefore might
be able to parse more programs.  For example, suppose that we want to
define a language LANGUAGE and that we have already defined its syntax
in a module LANGUAGE-SYNTAX.  Before even attempting to define the
semantics, it is a good idea to test the syntax by parsing a large
variety of programs.

In the examples provided with the tool, programs are generally kept in
a subdirectory in the directory containing the syntax definition.

As explained in detail in the papers about K, the entire language
syntax is automatically included as constructors for the builtin sort
K of computation structures, or simply just computations.  Concrete
syntax plays no role whatsoever in the mathematical foundations of K.
That means, in particular, that the distinction between
concrete/abstract syntax and its representation as computations of
sort K is irrelevant in the theory of K.  However, it becomes quite
relevant in implementations of K tools, because we want to use the
defined language syntax as much as possible in the semantics, which
means that we need to combine a parser for the defined language with a
parser for K in order to parse the semantic rules.  It is also possble
to use an external parser for programs in K; type `krun --help`.

In our current implementation of K, the internal representation of the
syntactic terms follows the simple abstract-syntax-tree (AST) syntax:

    K ::= KLabel "(" KList ")"

`KList` is a non-terminal standing for lists of K terms.  We use
`.KList` for the unit of KList.  This way, from an internal representation
point of view, a language syntax is nothing but a finite set of `KLabel`
constants.  The `kast` tool can be used to parse a program and see its
KAST form.  By running

    $ kompile simple-untyped.k
    $ kast tests/diverse/factorial.simple

from the [tutorial/2_languages/1_simple/1_untyped](/tutorial/2_languages/1_simple/1_untyped)
directory, you get the internal representation of the factorial program.
Typically, you should not need to execute the `kast` tool directly, as it will
be executed by the `krun` tool (below) when necessary.  However, executing it
directly can be useful to test and understand your syntax.

Our current implementation allows you to use either concrete syntax or
abstract syntax (as displayed by the `kast` command above) in your
semantic rules.  We typically prefer the concrete syntax, but you may
need to use the abstract syntax instead when your syntax confuses the K parser.


#### Running Programs

The `krun` tool can be used to execute programs, or explore their
behaviors.  What the `krun` tool basically does is:
1.  put the internal representation of the program in the initial
    configuration described in the definition;
2.  call the rewrite engine to execute the program by rewriting the
    resulting initial configuration; and
3.  post-process the output of the rewrite engine and display it in
    a more appealing format.

To run our sample program `factorial`, all we need to do is:

    $ kompile simple-untyped.k
    $ krun tests/diverse/factorial.simple --output none
    Input a natural number: 5
    Factorial of 5 is: 120

The `--output none` option tells `krun` to not display the
configuration.  Instead, it only displays output produced by the
program.  Try running it without this option to see the resulting
configuration.

You can also use the krun command to search for all possible final
states which could be obtained upon running the program, to model
check non-deterministic or concurrent programs, and even to
deductively verify programs.  These are all explained in the various
lectures in the tutorial.


## Reporting Issues/Bugs/Feature requests

Please report issues at <https://github.com/kframework/k/issues>.
Simply post your test case and briefly explain your problem.  If you
have write permissions to our repository, please also add a test case
to the repository yourself using the directions in
[tests/issues](/tests/issues/) (do this in addition to posting an issue,
because you need the issue number).
