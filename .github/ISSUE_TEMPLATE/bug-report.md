---
name: Bug report
about: Create a report to help us improve
title: "[Bug] [kompile|kast|krun|kprove|ksearch] - DESCRIPTION"
labels: bug
assignees: ''

---

**Categorize the bug**
Fill in the title above (template provided).

**Describe the bug**
A clear and concise description of what the bug is. Example:

Running `kompile` with `--some-weird-option` causes a cryptic error message.

Running `krun` with a definition causes a segfault on LLVM backend.

**Input Files**
All files needed to produce the bug. Example:

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

**To Reproduce**
Steps to reproduce the behavior (including _code blocks_ with what to run, and _code blocks_ with resulting output). Example:

Kompiling produces the weird error:

```
$ kompile --backend llvm --some-weird-option test.k
SOME_WEIRD_ERROR_MESSAGE
```

Running causes a segfault:

```
$ krun input.test
Aborted: some cryptic LLVM backend stuff. Segfault. Panic.
```

**Expected behavior**
A clear and concise description of what you expected to happen. Example:

`kompile` should be able to handle `--some-weird-option` without crashing.

`krun` should fail more gracefully and tell me it's because of a division by zero instead of segfaulting.
