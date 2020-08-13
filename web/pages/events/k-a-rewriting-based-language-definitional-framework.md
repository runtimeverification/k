# K: A Rewriting-Based Language Definitional Framework

Tutorial at the 33rd ACM SIGPLAN International Conference on Programming Language Design and Implementation (PLDI)

- June 16, 2012 – Beijing (China)
- Presenter: [Grigore Rosu](../people/grigore_rosu.md) (the main designer of K)
- Duration: Half a day
- Expected participants: ~20

## Description

K is an executable semantic framework in which programming languages, calculi, as well as type systems or formal analysis tools can be defined. K is a suitable framework for defining truly concurrent languages or calculi, even in the presence of sharing. Since computations can be handled like any other terms in a rewriting environment, that is, they can be matched, moved from one place to another in the original term, modified, or even deleted, K is also suitable for defining control-intensive language features such as abrupt termination, exceptions, or call/cc. K has been used to define real world languages like [C](http://c-semantics.googlecode.com/).

This tutorial will provide participants with a basic knowledge of the framework, as well as hands-on experience with using K to define a real programming language. Definitional techniques available in K, as well as comparisons of such techniques with other formalisms will be described. Time will be spent showing how one can automatically generate an interpreter, debugger, state space search, and a model checker from a single semantic definition. After attending the tutorial, participants will be able to use K to define their own languages or calculi and then derive similar tools from their semantics for free.

## Relevant Links

- http://k-framework.org: The main page for the K framework (see the Quick Overview section for a movie, demo and slides).
- http://k-framework.googlecode.com: The Googlecode page for the K tool.

## Tutorial format

Material and instructions will be provided to participants to load software and examples on their laptops. The presenter will give background material and an introduction to K, then the majority of the time will be spent working through examples in the K tool. The examples will be used to demonstrate both features of K, as well as design decisions that must take place when defining a language. Participants will be encouraged to examine and understand the example languages, then guided through making their own changes/improvements to those languages.

## Expected audience

The audience should be interested in practical aspects of programming language semantics. This includes interest in semantics as objects to be created/studied, as well as interest in the using such semantics for different program analyses. They need no previous knowledge, although a basic understanding of other definitional styles (such as SOS or evaluation contexts) may be helpful.
