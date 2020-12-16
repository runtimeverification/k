---
name: Bug report
about: Create a report to help us improve
title: "[Bug] [kompile|kast|krun|kprove|ksearch] - DESCRIPTION"
labels: bug
assignees: ''

---

First fill in the title (template provided).
Examples:

[Bug] kompile - crash when compiling with --some-weird-option

[Bug] krun - segfault at runtime when dividing by zero

K Version
---------

Tell us what version of K you are using.

Example:

```
$ kompile --version
RV-K version 1.0-SNAPSHOT
Git revision: 1bd3a49
Git branch: UNKNOWN
Build date: Sat Jul 11 01:41:19 UTC 2020
```

Description
-----------

A clear and concise description of what the bug is.
Examples:

Running `kompile` with `--some-weird-option` causes a cryptic error message.

Running `krun` with a definition causes a segfault on LLVM backend.

Input Files
-----------

*Minimized* files needed to produce the bug.
When providing K definitions, a _single_ file should be provided (if possible), and as few modules and sentences as possible.
When providing programs or proofs, a _single_ program should be provided with a minimized definition which _quickly_ reproduces the issue.

The definition should be as deterministic as possible: ie, the semantics should not behave differently depending on the order rules apply in, or based on the output of a hooked function that is impure, unless it is absolutely necessary in order to reproduce the bug (e.g. because the bug pertains to such a hook or to nondeterminism itself).

Examples:

File: `test.k`

```
module BADMODULE
   improts BAD-IMPORT
endmodule
```

File: `input.test`

```
bad-program ;
for i in [1,2,3]:
   print('hello')
```

Reproduction Steps
------------------

Steps to reproduce the behavior (including _code blocks_ with what to run, and _code blocks_ with resulting output).
Examples:

Kompiling produces a weird error:

```
$ kompile --backend llvm --some-weird-option test.k
SOME WEIRD ERROR MESSAGE
```

Running on LLVM backend causes a segfault when division by zero:

```
$ kompile test.k --backend llvm
Successful kompilation
$ krun input.test
Aborted: some cryptic LLVM backend stuff. Segfault. Panic.
```

Expected Behavior
-----------------

A clear and concise description of what you expected to happen. Example:

`kompile` should be able to handle `--some-weird-option` without crashing.

`krun` should fail more gracefully and tell me it's because of a division by zero instead of segfaulting.
