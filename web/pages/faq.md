# FAQ

## General questions

### What is K?

[13 Dec, 2013] K is a framework for defining programming languages. Once you define a language, K gives you a series of tools for that language, such as: a parser, an interpreter, a state-space explorer (like a model-checker for reachability), and even a deductive program verifier. We continuously work on making these tools better and on adding new tools.

### What is a language definition?

[13 Dec, 2013] A language definition consists of two parts: syntax and semantics. The syntax is defined using a [BNF](http://en.wikipedia.org/wiki/Backus%E2%80%93Naur_Form)-style, enriched with several features to ease the semantics. The semantics tells what each language construct is meant to do. This way, a language definition says both how the programs in your language should look like and also what they mean, or how they execute.

### What is the difference between a definition and an implementation?

[13 Dec, 2013] No difference in K. We think of K definitions as formal, rigorous implementations of the language. In fact, many users of K have no background on programming language semantics, they think of K as a domain-specific language for implementing programming languages. The benefit of implementing your language in K is that you can make use of the tools that K offers, which is not possible when you implement your language in a conventional programming language.

### Why K?

[13 Dec, 2013] There was and still is a considerable amount of effort spent by many scientists on developing parsing, model-checking, program verification and other formal program analysis techniques. Most of these techniques are language independent, yet a considerable amount of effort is then spent on developing language-specific tools based on these techniques. For example, developing a model-checker or a program verifier for Java, or C, or Python, is a serious endeavor, that only very few highly-skilled people can attempt. We believe that all these language-specific tools can be automatically derived from the K language definition, so that language designers spend the time only once to define their language and then get not only an implementation of their language, but also all the other tools, essentially for free.

## What is the difference between K and ...

### SDF

[13 Dec, 2013][sdf](http://www.program-transformation.org/Sdf/WebHome) is a parser generator. Simply speaking, it takes as input a grammar written in the SDF format and a text, and creates the abstract-syntax tree of that text corresponding to the grammar specification. K currently uses SDF for its parsing needs, but we integrated it into a more complex environment suitable for semantic definitions. Using the same language specification, we generate multiple parsers for different purposes: parse programs, parse rewrite rules, etc. Another difference is that we changed a bit the syntax of the grammar specification. We adopted a [BNF](http://en.wikipedia.org/wiki/Backus%E2%80%93Naur_Form)-style notation whereas SDF uses an algebraic specification, but we keept the same disambiguation system with priorities and associativity filters.

### Maude

### PLT Redex

[16 Dec, 2013][plt redex](http://redex.racket-lang.org/) is a language definitional framework based on [reduction semantics](http://en.wikipedia.org/wiki/Operational_semantics#Reduction_semantics) with evaluation contexts, a type of Structural Operational Semantics. A PLT definition consists of the syntax for the language (including the syntax of the execution configuration, if needed), followed by a syntax for evaluation contexts which allows identifying the next reducible expression (redex). The rules can specify the parts of the context (and abstract parts of it using variables), and can alter both the redex and the context. PLT Redex offers a suite of tools built on top of the Racket Scheme-based IDE to help visualize and explore executions. K borrows from PLT Redex the idea of evaluation contexts, and extends it further allowing more complex conditions be put on them. A distinctive difference between Redex and K is the fact that in K evaluation contexts are used only for the computational fragment of the executing configuration, the rules applying modulo the configuration abstraction. This, for example, allows K to more easily specify synchronous communication of agents or threads.

### Spoofax

### Rascal

### OTT

### ATL and Model-Driven Engineering

[14 Dec, 2013][atl](http://wiki.eclipse.org/M2M/Atlas_Transformation_Language_(ATL)) (Atlas Transformation Language) falls in the Model-Driven Engineering (MDE) field and includes a model transformation language and toolkit. ATL is also based on rules, which provide a means to produce a target model Mb conforming to a meta-model MMb, from a source model Ma conforming to a meta-model MMa. It should not be difficult to define such model transformations using K, this way effectively using the target meta-model MMb to give semantics to the source meta-model MMa. Moreover, if MMa and MMb have K semantics themselves, then the K tool can be used for proving the conformance of the transformation. Note, however, that K does not currently supply any explicit support for meta-model technologies, such as EMF (Eclipse Modelling Framework), etc.
