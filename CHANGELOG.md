K Framework 5.1.0
=================

Features
--------

-   Use the `claim` keyword instead of `rule` for proof obligations.
-   Bison parser is full-featured and supports external ahead-of-time `macro` and `macro-rec` expansion.
-   The new `krun` pipeline is written in `bash`, and can often skip running the Java frontend altogether.
    In particular, if `kompile` is called using the Bison parser (`--gen-bison-parser` or `--gen-glr-bison-parser`), you get this benefit.
-   K semantic version numbers are re-introduced, and can be expected to increment (rather than relying on git commit IDs).

K Framework 5.0.0
=================

Major changes since version 3.6, not all are documented here.
In particular:

-   No longer user Maude backend for K.
-   OCaml backend was developed, but now is being deprecated in favor of LLVM backend for concrete execution.
-   Java backend was developed, but now is being deprecated in favor of Haskell backend for symbolic execution.
