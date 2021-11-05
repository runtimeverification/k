K Framework 5.2.0
=================

**TODO**: Current as of 361eb5fe325b31d3bef049bda1c4e32a11d50ae5

Features
-------

- `kompile` will now attempt to simplify constant expressions which appear
  in the RHS of rules.

- The LLVM backend now supports the non-deterministic `search` feature.
  This must be enabled at `kompile` time with `--enable-search --backend llvm`
  and only supports the `--search|--search-final` options.

- The sentence type `imports syntax` has been removed. It was only used in one
  place in the tutorial, which was easy to resolve. This allows simplifying
  several code-paths in `kompile`.

- All modules which contain `configuration` declarations will automatically
  import the `MAP` module now, instead of only the main module.

- The new Haskell backend hooks for `encodeBytes` and `decodeBytes` are
  exposed in `domains.md`.

- Added support for module signatures supporting public/private syntax and imports.

- `macro` is now expected to be added to the syntax declaration instead of rules.

- Rework timing info for `--profile-rule-parsing`. It now takes a file and
  includes separate data fields for parsing and type inference.

- Added `kprovex`. A lightweight version of `kprove` which restricts the spec files
  to claims and token syntax. This avoids several bugs in the old code path and
  slightly improves the front end overhead. To convert the old tests, you need to
  kompile ahead of time the definition with the simplification rules and extra
  helper syntax needed for the proofs.

Documentation
-------------

- Relicence as BSD 3-Clause

- Lessons Basic 2-21 of the new K tutorial have been written.

- The option `--help-experimental` or `-X` is removed from all tools, and 
  all the `--help` option lists are flattened.

- Rename `pending-documentation.md` into `USER_MANUAL.md`

Misc/Bug Fixes
--------------

- Modules marked as `not-lr1` are automatically excluded from the generated
    Bison parser, instead of causing an error.

- `krun` respects the `--no-exc-wrap` option now.

- Formatting of several error messages is improved, especially indentation.

- File symlink handling in `requires` statements is improved.

- `kast` tool no longer silently ignores the `--output-file` parameter.

- Verbose mode offers more information about timings and scanners being created.

- Added `-I`, `--md-selector` and `--no-prelude` to kprove, kprovex and kbmc

Performance Improvements
------------------------

- Definition parsing performance is significantly improved by being smarter
  with the existing caches and optimizing some specific code hotspots.

- Improve type inference time for anonymous variables.

- Parse Record Productions in linear time.

- The K formula calculating Array extension has been optimized in `domains.md`.

Packaging/Deployment
--------------------

-   The Nix packages are built with LTO turned on. Bison is included
    in the Nix package dependencies. `kserver` now works on Nix.

-   The platform independent K binary, which really would only realistically
    work with Ubuntu Bionic (18.04), has been removed as an install option.

-   The Arch linux Dockerfiles have been updated for new Arch docker image
    naming scheme.


Dependency Updates
------------------

-   Haskell backend is updated to version d4239d97f5b53188460e7399b683111b5687661c.

-   LLVM backend is updated to version 23c2adcd21a1486442062ecc4ae051548215bcc3.

-   K Web Theme is updated to version b458d1461c31760024ea06e0e50f25806ace5e2c.

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
