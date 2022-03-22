K Framework 5.3.0
=================

Features
--------

- Moved the main repository from `kframework/k` to `runtimeverification/k`

- Removed the Ocaml backend.

- Added options to modify llvm-kompile's parameters in the Kompile frontend.

- Added support for `--pattern` passed to krun when you use the llvm backend.
  This delegates the search pattern matching to the haskell backend.

- `Bytes` literals are now supported natively by the K syntax.

- `kprovex` now supports function/functional simplification rules in the spec file.
  This makes it so you don't have to call kompile if you need to add only simplification
  rules to the spec file.

- `kprovex` can now print the specification file as JSON with the option `--emit-json-spec`

Misc/Bug Fixes
--------------

- Check for existential variables in requires clause. Dissallowed since it is considered
  LHS of the rule.

- Fixed an issue with the eoncding/decoding of anonymous variables in KORE (`decodeKoreString`)

- Fixed an issue where parsing an empty program would throw an `ArrayIndexOutOfBoundsException`.

- Improve checks for format attributes.

- Fixed an issue with `kparse` where it would truncate the output.

- Fixed various issues with the `--version` option.

- Fixed priority of `#let` relative to user syntax.
  Right now we have `_:Int > user-syntax > #let > ~> > =>`

- Allow macros on hooked sorts

Performance Improvements
------------------------

- Improved type inference for anonymous variables

- Caching some of the scanners when running `kprovex`

Dependency Updates
------------------

- Haskell backend is updated to version [ed00c99](https://github.com/runtimeverification/haskell-backend/tree/ed00c99446ef93d291ef651719ae5c634b7cf36e).

- LLVM backend is updated to version [2ac7270](https://github.com/runtimeverification/llvm-backend/tree/2ac72701a91c6c3ff15f65ab425a3674164cf18d).

- K Web Theme is updated to version [b458d14](https://github.com/runtimeverification/k-web-theme/tree/b458d1461c31760024ea06e0e50f25806ace5e2c).

- Require Z3 4.8.11 or higher

- Require Java 11 or higher

A more detailed list of changes can be found here:
https://github.com/runtimeverification/k/issues/2325

K Framework 5.2.0
=================

Features
--------

- Added `kprovex`. A lightweight version of `kprove` which restricts the spec files
  to claims and token syntax. This avoids several bugs in the old code path and
  slightly improves the front end overhead. To convert the old tests, you need to
  kompile ahead of time the definition with the simplification rules and extra
  helper syntax needed for the proofs.

- `kompile` will now attempt to simplify constant expressions which appear
  in the RHS of rules.

- `krun` now supports `--search` and `--search-final`. This works with the LLVM
  backend and must be enabled at `kompile` time with `--enable-search --backend llvm`.

- The sentence type `imports syntax` has been removed. It was only used in one
  place in the tutorial, which was easy to resolve. This allows several code-paths
  in `kompile` to be simplified.

- All modules which contain `configuration` declarations will automatically
  import the `MAP` module now, instead of only the main module.

- The new Haskell backend hooks for `encodeBytes` and `decodeBytes` are
  exposed in `domains.md`.

- Added support for module signatures supporting public/private syntax and imports.

- `macro` is now expected to be added to the syntax declaration instead of rules.

- Rework timing info for `--profile-rule-parsing`. It now takes a file and
  includes separate data fields for parsing and type inference.

Documentation
-------------

- Relicense as BSD 3-Clause

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

- Added `-I`, `--md-selector` and `--no-prelude` to `kprove`, `kprovex` and `kbmc`

Performance Improvements
------------------------

- Definition parsing performance is significantly improved by being smarter
  with the existing caches and optimizing some specific code hotspots.

- Improve type inference time for anonymous variables.

- Parse Record Productions in linear time.

- The K formula calculating Array extension has been optimized in `domains.md`.

Packaging/Deployment
--------------------

- The Nix packages are built with LTO turned on. Bison is included
  in the Nix package dependencies. `kserver` now works on Nix.

- The platform independent K binary, which really would only realistically
  work with Ubuntu Bionic (18.04), has been removed as an install option.

- The Arch linux Dockerfiles have been updated for new Arch docker image
  naming scheme.

Dependency Updates
------------------

- Haskell backend is updated to version [82b8a19](https://github.com/kframework/kore/commit/82b8a19bfc3fb7d9f3ca3f3e715ec7ae08b70a99).
  
- LLVM backend is updated to version [572cf69](https://github.com/kframework/llvm-backend/commit/572cf698be6baef5cdd01aa9239e32e9be89ec6a).

- K Web Theme is updated to version [b458d14](https://github.com/runtimeverification/k-web-theme/commit/b458d1461c31760024ea06e0e50f25806ace5e2c).

- JavaCC is updated to version 4.1.4.

- commons-io Java library is bumped to version 2.7.

A more detailed list of changes can be found here:
https://github.com/runtimeverification/k/issues/1697

K Framework 5.1.0
=================

Features
--------
- Use the `claim` keyword instead of `rule` for proof obligations.

- Bison parser is full-featured and supports external ahead-of-time `macro`
  and `macro-rec` expansion.

- The new `krun` pipeline is written in `bash`, and can often skip running the
  Java frontend altogether. In particular, if `kompile` is called using the Bison
  parser (`--gen-bison-parser` or `--gen-glr-bison-parser`), you get this benefit.

- K semantic version numbers are re-introduced, and can be expected to increment
  (rather than relying on git commit IDs).

K Framework 5.0.0
=================

Major changes since version 3.6, not all are documented here.
In particular:

- No longer user Maude backend for K.

- OCaml backend was developed, but now is being deprecated in favor of LLVM
  backend for concrete execution.

- Java backend was developed, but now is being deprecated in favor of Haskell
  backend for symbolic execution.
