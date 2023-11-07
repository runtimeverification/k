---
copyright: Copyright (c) K Team. All Rights Reserved.
---

K Framework 6.1.0
=================
TODO: remove me updated up to version 6.0.162 1b12ea45f617b081b1b095287e9c1514312e5571

Features
--------
- Added support for MacOS 13 Ventura and Debian 12 Bookworm. We dropped support for
  Ubuntu 20 Focal. You can now build K from sources on Apple Silicon. See README
  for more details.

- Updated dependency to Java version 17 or higher.

- Added the Haskell Backend Booster as a dependency to K. This can improve performance
  when running large proofs. It combines the llvm-backend for concrete execution and
  relies on the haskell-backend to simplify terms when there is a split in the proof.

- Optimized the kompiler by removing unit applications for collections.

- Minimize JSON output by dropping unused attributes

- Added `--smt-timeout` flag to `krun` and `kprove`.

- Changed the Maven repository to Cloudrepo for more stability and flexibility when
  building K from sources.

- Improved attribute error messages by creating a whitelist dependent on the context.
  This check is now mandatory.

- Rule label cannot contain ` or whitespace

- Improved the help messages by adding a description of the expected parameter.

- Documentation: Started work on Section 2 of the tutorial. Added a description for
  `kserver`.

- Added `--debugger-command` flag to krun.

- Added two options `--debug-tokens` and `--debug-parse` to help with debugging
  parsing errors. The first option will print a Markdown table with all the matched
  tokens by the scanner. The second one will give more details about the partial parse
  tree constructed before an error was encountered.

Misc/Bug Fixes
--------------
- Fixed a bug where the llvm backend would segfault because of badly initialized
  fresh variables in the configuration.

- Improved performance for JSON creation.

- Remove old unused attributes.

- Fix output sorting for KPrint. This will create a more stable pretty printed output.

- Fix configuration pretty printing where `<generatedCounter>` would appear instead
  of a closing cell.

- Moved a README file from the `builtin` directory that could collide with users' files.

A more detailed list of changes can be found here:
https://github.com/runtimeverification/k/issues/3706

K Framework 6.0.0
=================

Features
--------
- Removed the Java backend. From now on, all symbolic execution will be handled by the
  haskell backend and concrete execution by the llvm backend. Alongside that we also
  removed the `kprove-legacy` and the `kbmc` tool. Bounded model checking capabilities
  have been added to the pyk library.

- Deprecated the `--directory` option. Use `--output-definition` to store a definition
  and `--definition` to load one.

- Introduced `--execute-to-branch` to `krun` when using the LLVM backend.

- Created a hidden category for advanced options: `--help-hidden`. This should make it
  easier to read the help menu for `kompile` and `kprove`.

- Added attribute validation. From now on, you will have to use `group(_)` to tag a
  production. You can still get the old behavior by providing `--no-pedantic-attributes`.

- Add `--temp-dir` option to specify where to store all the temp files created at
  runtime. This can avoid some issues with accumulating files and readonly restrictions.

- Added a new builtin type `RangeMap`, a map whose keys are stored as ranges, bounded
  inclusively below and exclusively above. Contiguous or overlapping ranges that
  map to the same value are merged into a single range.

Misc/Bug Fixes
--------------
- Fix some issues related to unicode characters not being parsed correctly.

- Total attribute is allowed only on function symbols.

- Added more checks and warning messages.

- Fix inconsistencies around the `comm` attribute.

- Fix KLabel checks to consider `--concrete-rules` option.

A more detailed list of changes can be found here:
https://github.com/runtimeverification/k/issues/3403

K Framework 5.6.0
=================

Features
--------
- Rename the attribute `functional` to `total` to better reflect its semantics.

- Updated `pl-tutorial` examples to work with the more modern backends: simple-untyped, kool, fun and logik.

- Pass through C build type option to llvm-kompile.

- Extended the syntax for code block annotations to allow for more decorators for web extensions.

- Added option `kompile --enable-llvm-debug` as a more easy to remember alternative to `-g -O1`.

- Improved LLDB debugging support for macOS.

- Added the `klsp` tool. It adds [Language Server](https://microsoft.github.io/language-server-protocol/) support for K.
  For now it supports: contextual code completion, go-to definition, find references, syntax error reporting
  and selection range. Has been tested with VSCode. You can find the
  [K Framework](https://marketplace.visualstudio.com/items?itemName=RuntimeVerification.k-vscode) extension on the marketplace.

Misc/Bug Fixes
--------------
- Fix an issue where #Exists would not bind variables in the LHS.

- Automatically import BOOL when strictness is applied.

- Update the check for duplicated modules. It now allows for file copy.
  It calculates a digest and looks for content changes.

A more detailed list of changes can be found here:
https://github.com/runtimeverification/k/issues/3260

K Framework 5.5.0
=================

Features
--------
- Improve error messages for erroneous simplification rules.

- Added the `kup` tool to help with keeping the various dependencies up to date.

- Documentation updates


Misc/Bug Fixes
--------------
- Relax module duplication check to allow for duplicate files. Useful when moving
  the original definition to a new location.

A more detailed list of changes can be found here:
https://github.com/runtimeverification/k/issues/3005


K Framework 5.4.0
=================

Features
--------

- Added `--definition` and `--output-definition` command line options for specifying the exact
  path for storing and loading from the kompiled definition.

- Print source lines in error messages.

- The haskell backend uses by default a new binary kore format. This decreases load time but
  can cause issues on certain systems (Apple Silicon). Use the `-no-haskell-binary` option to
  fall back to the textual format.

- Renamed `kprovex` to `kprove` and `kprove` to `kprove-legacy`.

- Introduced V2 of the JSON kast format. Better handling for `KLabel` parameters and sorts.

- Add error message for duplicate user lists.

- Added `#trace` to the list of IO operations to aid in debugging.

- Added `--post-process`, a JSON KAST => JSON KAST converter to run on the definition after
  kompile pipeline. The [pyk](https://github.com/runtimeverification/pyk/tree/master/pyk-tests/post-process)
  library offers a convenient collection of operations for quick prototyping.

- Adding the `comm` attribute on a simplification rule will now generate a similar rule
  with the top most LHS function reversed. The syntax declaration also needs this attribute.
  
- LLDB can now be used for debugging the llvm-backend on OSX.

- The `kast` tool now allows access to the rule grammar by providing `--input rule`.

- Added more claims filtering options for `kprove`: `--trusted`, `--exclude` and `--claims`.

- Various improvements to error messages and made it easier to debug and profile a definition. 

Performance Improvements
------------------------

- Optimize grammar generator steps.

- Optimize the type inference step by reducing the work done by Z3.

Misc/Bug Fixes
--------------

- Make generated anonymous variables parsable (`_0` => `_Gen0`).

- Outer parser returned off by one end-column.

- Bad parameters to kompile and kprove are now corectly reported as errors.

- Fix the Bison parser not handling Bytes correctly.

- Use clang by default on OSX

- `--emit-json-spec` now can print out multiple modules.

Dependency Updates
------------------

- Haskell backend is updated to version [efeb976](https://github.com/runtimeverification/haskell-backend/tree/efeb976108a0baa202844386193695564a257540).

- LLVM backend is updated to version [5001b5b](https://github.com/runtimeverification/llvm-backend/tree/5001b5b294bab59db6034c79e92bbd71b1746666).

- K Web Theme is updated to version [f670742](https://github.com/runtimeverification/k-web-theme/tree/f67074272c1513e8194c7653f8bbdef0b293f4ee).

- Require Z3 4.8.15 or higher

- Downgrade Calibre to 5.42.0

A more detailed list of changes can be found here:
https://github.com/runtimeverification/k/issues/2514


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

- The LLVM backend now supports binary KORE representation. This can have a significant speed
  benefit on large definitions.

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

- LLVM backend is updated to version [4dedab7](https://github.com/runtimeverification/llvm-backend/tree/4dedab70ede89d4a5fb637d287f8ccf5bb89d499).

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

- No longer uses Maude backend for K.

- OCaml backend was developed, but now is being deprecated in favor of LLVM
  backend for concrete execution.

- Java backend was developed, but now is being deprecated in favor of Haskell
  backend for symbolic execution.
