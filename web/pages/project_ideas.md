# Project Ideas

## Introduction

### Overview

K is a framework for designing new programming languages and formalizing existing ones. K is unique in that the framework scales to very large languages like C (see the [C semantics](https://code.google.com/p/c-semantics/) project) and has good tool support (see the [K tool](https://code.google.com/p/k-framework/)). To get a quick taste of K, see our [5-minute demo](./news/k-framework-demo.md). To understand it better, do the [K Tutorial](./tutorials.md). For an overview of the tool, see [The K Primer (version 2.5)](<http://fsl.cs.illinois.edu/index.php/The_K_Primer_(version_2.5)?action=render>); for a theoretical overview, see [An Overview of the K Semantic Framework](http://fsl.cs.illinois.edu/index.php/An_Overview_of_the_K_Semantic_Framework?action=render).

This page lists project ideas related to the K framework. Although this page was initially created for [Google Summer of Code](https://code.google.com/soc/) students, it is applicable to any student interested in working with K. Students viewing this page will also be interested in the [current list of projects](./projects.md) using K and the [GSoC2013](http://fsl.cs.illinois.edu/index.php/GSoC2013?action=render) information page.

**Remember**: Students are not limited to projects on this list! We encourage students to submit proposals for their own ideas. We also encourage students to discuss their ideas with us before submitting a proposal, either via IRC (#fsl on [freenode](http://freenode.net/irc_servers.shtml)) or our [mailing list](http://lists.cs.uiuc.edu/mailman/listinfo/fsl-gsoc).

### Structure of the Ideas list

Besides a description, each project below has some additional information to help students select a project.

#### Color

<span style="color:#4CAF50;">Green projects</span> are primarily coding projects and don't require much theoretical background to get started.

<span style="color:#2196F3;">Blue projects</span> are like green projects, except require more theoretical background and theoretical insights. These projects may require you to read a paper or two.

<span style="color:#F44336;">Red projects</span> are potential research directions but are too large and complex for GSoC. They are included to give a flavor of future directions of our work.

#### Scale

Most project ideas also specify a Scale. The following Scales are used (assuming the student is working on the project full-time):

**Summer**: The project can definitely be completed over the summer.

**Summer+**: The project can be completed over the summer by an ambitious student.

**Summer++**: The project will require extra time beyond the summer to fully complete, but a usable portion of the project can be completed over the summer.

#### Prerequisite experience

For each project idea there is some implicit prerequisite experience. All of the projects require a minimum understanding of what K is, its goals, and the structure of the tool. Tool developers will need to know Java and how to work with ASTs in Java, but will not need to be as familiar with the theory or features of K. Developers of K definitions wont need to know Java, but will need to become more familiar with the theory and features of K. Projects may have additional experience prerequisites specified below.

#### Probable mentors

Most project ideas specify a list of people that are likely to mentor the project. See the [People](./people.md) page for a list of potential mentors for all projects and links to their homepages. Note that a project idea without mentors does not mean that there are no mentors available for the project; it means the mentors will be assigned based on the student's proposal.

## Ideas

### User interfaces

#### <span style="color:#4CAF50;">Eclipse IDE</span>

Integrate the K Semantic Framework with Eclipse to make the framework more accessible and user-friendly. Features we would like in the K/Eclipse IDE include:

- Ability to edit, compile, and execute semantics without ever having to leave Eclipse. This would require integration with the compile scripts and the K backends. One possibility is to embed the Maude interpreter into Eclipse.
- Syntax highlighting for K modules.
- When typing a cell start tag like "<k>", the end tag "</k>" should automatically be inserted.
- Autocompletion for cell names, sorts, operators, module names, etc.
- Integration with static analysis tools. For example, the IDE should add yellow "warning" underlines to indicate named variables on the LHS of a rule that are not used in the RHS.

**Scale**: Summer+  
**Prerequisite experience**: Java. Familiarity with developing Eclipse plug-ins. UI design experience.  
**Probable mentors**: Grigore, Dorel

#### <span style="color:#4CAF50;">Web interface for K</span>

A web interface for K allows users to learn about and use K without having to install it first. Improve the [existing online web interface](https://fmse.info.uaic.ro/tools/K/) or (preferably) create a new online interface from scratch. One possibility is to emulate a terminal in the browser that accepts commands that are identical to the commands that would be used to run K locally.

**Scale**: Summer+  
**Prerequisite experience**: Web programming experience.  
**Probable mentors**: Andrei, David

#### <span style="color:#2196F3;">GUI for creating programming languages</span>

Due to the modularity of the K framework, language features (e.g., side effects, exceptions, threads, continuations, type systems, etc.) can easily be added and removed from a language. Build a GUI that exposes this modularity by letting users create custom programming languages easily. One possibility is to create an interface which allows language features to be combined via drag-and-drop. Regardless, the GUI should support:

- Lots of language features
- Customizable syntax for every language feature
- Running programs in the custom language directly in the GUI
- Any other features you may think of

**Scale**: Summer++  
**Prerequisite experience**: UI design experience.  
**Probable mentors**: Grigore

### Derived tools

Multiple tools can be automatically derived from a single K definition of a language:

- Interpreter: given a program, execute it
- State space search tool: given a program, search for all of its possible behaviors
- Debugger: given a program, step through its execution with breakpoints, watchpoints, etc.
- Definedness checker: given a program, determine whether it is defined or not according to the semantics
- Coverage checker: given a program or a collection of programs, determine how frequently each K rule is used to execute the program(s). This is used to check the coverage of a compiler's test suite.
- Profiler: given a program, run it and determine which rules are executed most often and which take the most time

The following projects involve improving these tools and making them general enough to work with all K definitions.

#### <span style="color:#4CAF50">Interpreter</span>

The krun tool allows a K definition to be used as an interpreter and state space search tool for the language it defines. For example, the command krun collatz.imp executes the collatz program using the definition of the IMP language. The goal of this project is to fix bugs and add features to the (Java version) of krun. One possible task is to add support for querying cells in the output configuration using XPath.

**Scale**: Summer  
**Prerequisite experience**: Java. Manipulating XML in Java. Experience with existing interpreters and debuggers.  
**Probable mentors**: David, Emilian

#### <span style="color:#4CAF50">Profiler</span>

The [C semantics](https://code.google.com/p/c-semantics/) project already has a profiler specific to C. Extract this tool from the C project and make it available to all K definitions. This will allow all users of K to benchmark their definitions and to profile programs that are executed in the definition.

**Scale**: Summer  
**Prerequisite experience**: Ability to read Perl (since the C profiling tool is written in Perl).  
**Probable mentors**: Chucky

#### <span style="color:#4CAF50">Visual stepper</span>

Create a variant of [Maude Stepper](http://fsl.cs.illinois.edu/index.php/Special:MaudeStepperOnline) that is specialized for K. This would let users execute programs visually, allowing users to explore a program's different behaviors by putting the language's non-deterministic choices in their hands. Ideally, this tool would easily integrate with a web interface for K or an IDE for K.

**Scale**: Summer  
**Prerequisite experience**: Experience with computer graphics and user interfaces is a big plus.  
**Probable mentors**: Traian

#### <span style="color:#2196F3">Automatic test case generation</span>

Create a tool that generates valid programs from a programming language's K definition. Students working on this project will need to come up with an ingenious idea for accomplishing this task.

**Scale**: Summer+  
**Probable mentors**: Chucky

### K definitions

#### <span style="color:#2196F3">Define an existing language</span>

Many _real_ programming languages have been formally defined in K, including C, Scheme, and Verilog. Formal definitions are also being developed for LLVM IR, Haskell, Javascript, and Python. This project involves giving formal semantics in K to an existing programming language. These are some examples of languages we think would be interesting to give formal semantics to and that would benefit the K framework:

- [LC-3](http://en.wikipedia.org/wiki/LC-3), an educational assembly language. We are interested in seeing more assembly languages defined in K.  
  **Scale**: Summer  
  **Probable mentors**: Chucky, David

- x86, a not-so-simple assembly language.  
  **Scale**: Summer

- Prolog. A logic programming language has not yet been defined in K.  
  **Probable mentors**: Traian

- Esoteric programming languages. Currently, K semantics exist for BF, Befunge93, Thue, and reMorse. K definitions for other esoteric languages are welcome.  
  **Scale**: Summer  
  **Probable mentors**: Chucky

- Dependently typed languages like Agda or Epigram. Several type systems and type inferencers have been defined in K, but no dependent type systems.  
  **Scale**: Summer+
  **Probable mentors**: David

- Lambda calculi. The idea behind this project would be to start by defining simply typed lambda calculus, then System F, and then moving on to define richer and richer lambda calculi until every vertex of the lambda cube is formally defined in K.  
  **Probable mentors**: Grigore, David

- SQL. This would be one of the few languages defined in K that is not Turing Complete.
  **Probable mentors**: Chucky

- Smalltalk
  **Probable mentors**: Chucky

- Ruby
- Your favorite programming language not listed above!

**Prerequisite experience**: Proficiency or expertise in the language to be defined.

#### <span style="color:#2196F3">Create a new language</span>

K is a tool for creating new programming languages, not just defining existing ones. If you have a great idea for a new programming language or Domain Specific Language (DSL), implement it using K! Your proposal for this project should include the merits of your new language and comparisons to existing languages.

**Scale**: Summer+  
**Prerequisite experience**: Some prior experience with language design. Proficiency in languages similar to the language you're creating.

#### <span style="color:#2196F3">Model other systems in K</span>

K is not limited to defining programming languages. For example, it has been used to model algorithms and problems in computer science. The [trunk/examples/algorithms](https://code.google.com/p/k-framework/source/browse/trunk/examples/algorithms) subdirectory in the K framework SVN contains executable K definitions of Dijkstra's algorithm and algorithms for solving the Sudoku puzzle, among other simple algorithms. What other algorithms or areas could K be applied to besides programming languages? Pick an algorithm or class of algorithms to define in K. Or attempt to model some other system entirely, for example:

- Circuits
- Hardware components (CPUs, ALUs, etc.)
- Network protocols (Ethernet, TCP/IP, DNS, etc.)
- Cryptographic protocols (Diffie-Hellman key exchange, Zero-knowledge proofs, SSH, etc.)

**Scale**: Summer-Summer+, depending on the algorithm(s)

### Frontends and backends

The current K tool has one frontend and two backends: a K definition can be compiled into Maude for execution, or it can be compiled into LaTeX for viewing. These projects involve creating new backends for K and improving the frontend.

#### <span style="color:#4CAF50">Java/SDF frontend</span>

The frontend parses K definitions (using [SDF](http://www.syntax-definition.org/)) and generates the K Intermediate Language code corresponding to the definition. Since a K definition contains multiple syntaxes, it is difficult to parse them accurately. Furthermore, most of the work in extending K happens in the frontend. This project involves fixing issues related to the frontend and adding features to K that primarily involve frontend work (see the [issue tracker](https://code.google.com/p/k-framework/issues/list)).

**Scale**: Summer  
**Prerequisite experience**: Parsing. Some experience with SDF.  
**Probable mentors**: Radu, Andrei

#### <span style="color:#4CAF50">Maude backend</span>

Currently, the compiler from K to Maude is written in Maude itself. Unfortunately, this Maude code is hard to extend and hard to maintain. Luckily, the compilation process is broken up into several self-contained source-to-source transformations. Replace each transformation that's written in Maude with an equivalent transformation in Java that operates on the K Intermediate Language (KIL).

**Scale**: Summer+  
**Prerequisite experience**: Ability to work with XML and ASTs in Java. Some experience writing a compiler is beneficial but not necessary.  
**Probable mentors**: Traian, Andrei

#### <span style="color:#2196F3">Ocaml or Haskell backend</span>

Although defining a language in K gives you an interpreter for free (via the Maude backend), this interpreter is usually not fast enough for general purpose use. By putting some restrictions on K rules, we have been able to compile K definitions into OCaml interpreters for a tremendous speed boost. See the [K Compiler](http://fsl.cs.illinois.edu/index.php/K_Compiler?action=render). Expand on this previous work in the following ways:

- Port the existing K Compiler to the current version of K, or start over from scratch using the existing compiler as a reference.
- Relax the restrictions put forth in the original tool: allow rules to be applied to arbitrary locations in K cells and add support for AC matching.
- See Future Work in [On Compiling Rewriting Logic Language Definitions into Competitive Interpreters](http://fsl.cs.illinois.edu/index.php/On_Compiling_Rewriting_Logic_Language_Definitions_into_Competitive_Interpreters?action=render).

**Scale**: Summer+  
**Prerequisite experience**: OCaml or Haskell.  
**Probable mentors**: Chucky, David

#### <span style="color:#2196F3">Coq or Isabelle backend</span>

Create a backend for K that compiles K definitions into a proof assistant language, such as Coq or Isabelle. This would allow us to formally reason (prove properties) about K definitions.

**Scale**: Summer+  
**Prerequisite experience**: Proficiency with Coq or Isabelle.  
**Probable mentors**: Brandon, Stefan

### Miscellaneous

#### <span style="color:#4CAF50">Static analysis tools for K</span>

As with any other programming language, mistakes can be made when writing K definitions. The scope of this project is to create a lint-like tool that detects (and possibly fixes) common errors that appear in K definitions. These can range from stylistic errors to more serious semantic errors:

- Named variables that don't appear on the "right-hand side" of a rule should be replaced with the anonymous underscore variable.
- Warnings should be issued for syntax that does not appear in any semantic rules.
- Rules that can lead to infinite rewriting (when the LHS of a rule appears on its RHS) should issue warnings.
- Find rules that do not maximize sharing and suggest how to fix them so that sharing between the LHS and the RHS is maximized.
- Issue warnings when deprecated conventions are used, causing new conventions to be adopted sooner.

**Scale**: Summer
**Probable mentors**: Chucky

#### <span style="color:#F44336">Deriving semantics using genetic algorithms</span>

Given the syntax of a programming language and an interpreter for it, can we use genetic algorithms to derive a semantics for the programming language?

**Scale**: Summer++
