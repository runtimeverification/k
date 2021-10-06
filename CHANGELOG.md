K Framework 5.2.0
=================

**TODO**: Current as of 30d285a8442b622796f8e2e212f92d4bec23029d

Feature Additions
-----------------

-   `kompile` will now attempt to simplify constant expressions which appear
    in the RHS of rules.

-   The LLVM backend now supports the non-deterministic `search` feature.
    This must be enabled at `kompile` time with `--enable-search --backend llvm`
    and only supports the `--search|--search-final` options.

Feature Removals
----------------

-   The sentence type `imports syntax` has been removed. It was only used in one
    place in the tutorial, which was easy to resolve. This allows simplifying
    several code-paths in `kompile`.

Kore Encoding and Builtins
--------------------------

-   The K formula calculating Array extension has been optimized in
    `domains.md`.

-   All modules which contain `configuration` declarations will automatically
    import the `MAP` module now, instead of only the main module.

-   The LLVM backend now also sees `simplification` rules, and is responsible
    for ignoring them.

-   The new Haskell backend hooks for `encodeBytes` and `decodeBytes` are
    are exposed in `domains.md`.

Documentation
-------------

-   The option `--help-experimental` or `-X` is removed from all tools, and
    all the `--help` option lists are flattened.

-   Documentation for `symbol`, `klabel`, `simplification`, and `smt-lemma`
    attributes is updated in `pending-documentation.md`. Documentation for
    the `#Layout` sort is updated in `kast.md`.

-   Lessons 2-12 of the new K tutorial have been written.

Parsing Performance
-------------------

-   Definition parsing performance is significantly improved by being smarter
    with the existing caches and optimizing some specific code hotspots.

Misc
----

-   Modules marked as `not-lr1` are automatically excluded from the generated
    Bison parser, instead of causing an error.

-   `krun` respects the `--no-exc-wrap` option now.

-   Formatting of several error messages is improved, especially indentation.

-   File symlink handling in `requires` statements is improved.

-   `kast` tool no longer silently ignores the `--output-file` parameter.

Packaging/Deployment
--------------------

-   The automatic deployment release trigger is fixed.

-   The Nix packages are built with LTO turned on. Bison is included
    in the Nix package dependencies. `kserver` now works on Nix.

-   The platform independent K binary, which really would only realistically
    work with Ubuntu Bionic (18.04), has been removed as an install option.

-   The Arch linux Dockerfiles have been updated for new Arch docker image
    naming scheme.


Dependency Updates
------------------

-   Haskell backend is updated to version 67d4d2369.

-   LLVM backend is updated to version 789d437.

-   K Web Theme is updated to version 4d2c931.

-   JavaCC is updated to version 4.1.4.

-   commons-io Java library is bumped to version 2.7.

A more detailed list of changes can be found here:
https://github.com/kframework/k/issues/1697

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
