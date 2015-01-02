<!-- Copyright (c) 2014-2015 K Team. All Rights Reserved. -->

# K Framework 3.6 #

## General ##
- Maude backend has been discontinued. Please try to convert your
  definition to the Java backend. If you run into trouble and a particular
  feature is not supported, please report the feature to us so we can fix it.
  Limited support for K 3.5 will continue until the release of K 4.0. We will
  backport bug fixes if necessary. K 4.0 will be released when the
  Java backend is deemed a suitable complete replacement for maude.

## KRun ##

- `krun --output raw` has been removed. If you are interested in disabling
  pretty-printing, it is recommended that you try `krun --output kast`.

## Developer API ##

- The KRunResult class has been removed. It contained two fields, `statistics`
  and `rawResult`. If you are developing a feature that cannot work effectively
  without one or both of these fields, please file an issue so that we can
  evaluate your case and attempt to come up with a new API.
- The `kompileOptions()` and `krunOptions()` methods of `AbstractKModule` now
  take a class literal instead of an object. The object is constructed from
  the class by dependency injection (i.e. via a 0-args or `@Inject`-annotated
  constructor)


# K Framework 3.5 (released 2014-12-19) #

## General ##
- Discontinued compatibility with Java 7.
- Added an API for users to extend the K framework by means of extending
  the interface KModule or the abstract class AbstractKModule. Support for:
    - Adding a new backend to Kompile.
    - Adding a new backend to KDoc (see section "Kompile" below).
    - Adding new options to kompile.
    - Adding new options to krun.
    - Adding new hooks to the Java backend.
- Added commands "kserver" and "stop-kserver" to create a local server
  to run K commands on, implemented using 
  [Nailgun](http://www.martiansoftware.com/nailgun/). The server
  is automatically enabled whenever `kompile`, `krun`, `ktest`, `kast`, or
  `kdoc` is run when the `K_NAILGUN` environment variable is set to a 
  nonempty string. Running applications with nailgun is an experimental
  feature, subject to certain bugs, but it can be used to increase the
  speed of executing K programs by a factor of 3-7x.
- Migrated build system from Ant to Maven. For information on building
  K, refer to the [developer README](src/README.md).
- Removed the `--backend symbolic` option from the distribution.
  UAIC in Iasi intends to support this functionality using the generic
  K plugin interface (see "General" above).
- Removed the `kagreg` tool from the distribution.
- Removed the `--debug-gui` KRun option from the distribution.

## K Language ##
- Changed the KLabel for UserList terminators to `'.List{"<KLabel>"}` 
  instead of `'.List{"<Separator>"}`. This allows for a broader range
  of syntaxes for user lists, as well as the possibility of custom
  KLabels.
- Changed the syntax of fresh variables from `rule foo => N when fresh(N:Int)`
  to `rule foo => ?N:Int`.
- Added a syntax for fresh constants: `rule foo => !N:Int`.
- Added a syntax for adding attributes to arbitrary terms:
  `<Term>::Sort{attributes}`
- KResult is now a subsort of KItem.

## K Standard Library ##
- Changed sorts List, Map, Set to be subsorts of KItem. The tool translates
  these K expressions into builtin lookups, updates, and selections on the
  underlying data structures.
- Changed the syntax of set inclusion: SetItem(1) in SetItem(1) no longer
  returns true. This is to distinguish between a set of elements and a set
  of sets.
- Removed operations ==Set, ==List, ==Map, =/=Set, =/=List, =/=Map. The
  correct syntax now is to use ==K for all of these.
- Changed the syntax of Map update from `Map [ Value / Key ]` to
  `Map [ Key <- Value ]`.
- Added a new Map difference operator `-Map`.
- Renamed Map update operator `updateMap`.
- Separated implementation of Map, List, Set, and MInt sorts from their
  specification in separate `-impl.k` files.
- Added syntax predicates isPascalCaseId and isCamelCaseId to refer
  to Ids which begin with an uppercase or lowercase letter respectively.
- Added a new builtin function #system which operates like the system()
  syscall.

## Parsing ##
- Added a type interencer based on context for the sorts of variables.
- Correct the behavior of associativity on productions not of the form
  `syntax Sort ::= Sort1 "op" Sort2`
- Added a new syntax for case insensitive terminals:
  `syntax Sort ::= 'terminal'`
- Added new attribute "noAutoReject" in order to allow users to provide
  an infinite set of tokens _not_ to reject.
- Removed the "cons" attribute which was an artifact of the SDF implementation.
- Added the `--java-parser` and `--java-parser-rules` options to test the
  experimental new parser written in Java.
- Added the K function `#parseInModule` which allows the user to parse input
  in the syntax of a particular K module.
- Added a friendly error message when the SDF parser crashes.

## Pretty Printing ##
- Added code which indents Map/List/Set elements from their parent collections.

## Kompile ##
- Added a new option `--legacy-kast` which preserves the old behavior of
  several pieces of functionality which were specific to the Maude
  implementation.
- `kompile --backend [pdf|latex|html|unparse|unflatten|doc]` has been
  moved to a new tool, `kdoc --format [pdf|latex|html|unparse|unflatten|doc]`
- Modules are required to import or declare constructors for sorts that they
  use. In the event of a circularity, a forward reference can be introduced
  using the syntax `syntax Sort` without any declared productions.
- Added prototype of `--backend coq`.
- Removed deprecated experimental options `--kore`, `--lib`, `--loud`,
  `--non-symbolic-rules`, `--symbolic-rules`, `--rule-index`, `--test-gen`.

## Kast ##
- The default output of `kast` when the `--legacy-kast` flag is not set on
  `kompile` is now the new KORE syntax which will be utilized by K 4.0.
  This allows users to write external parsers that output this syntax
  in the Java rewrite engine, a previously unsupported feature.
  For information about the new syntax, refer to
  [the syntax of KORE](https://github.com/kframework/k/blob/kast-in-K/samples/kast/kore.k). Currently 
  only the KSEQ module is supported by the parser.

## KRun ##
- Using JCommander to parse KRun options. See notes for version 3.4 under
  "Kompile" for details.
- Added option `--coverage-file` to tell KRun to output rule coverage
  information.
- Added code to normalize the values of semantic variables in the output
  of KRun.
- Added support for greater configuration of KRun output modes, including
  using `--output` combined with `--debugger` and others.
- Added new output mode "kast" to represent un-concretized KAST terms.
- Changed syntax for setting a command line parser from 
  `--config-var-parser <parser> -cPGM=<term>` to `-pPGM=<parser> -cPGM=<term>`.
- Removed option `--backend`. Backend is now specified in kompile and read
  from the compiled definition.
- Removed deprecated options `--main-module` and `--syntax-module`. These values
  are now read from the compiled definition.
- Renamed option `--debug-info` to `--debug` for consistency with other tools.
  Previous `--debug` for the debugger was renamed to `--debugger`.
- Changed option `--ltlmc` to accept only formulas. A file may be specified
  with the `--ltlmc-file` option.
- Removed deprecated experimental options `--index`,
  `--indexing-stats`, `--generate-tests`, `--load-cfg`.

## KTest ##
- Improved the output of KTest to display a message for each running
  process only when that process is actually run.
- Add a "Running" message to KTest for compilation and pdf generation stages.
- Fixed a minor display issue when using `ktest --dry`.
- Using JCommander to parse KTest options. See notes for version 3.4 under
  "Kompile" for details.
- Improved parallelism of KTest by using a common task queue for all
  processes to be run.
- Changed ordering of KTest execution to execute programs for each definition
  immediately following compiling that definition.
- `ktest --debug` now propagates `--debug` to the `kompile`, `kdoc`, and
  `krun` processes it generates.

## Java Rewrite Engine ##
- Significant improvements to the performance and stability of the rewriter.
- Support for rules tagged "anywhere" as long as they rewrite a KItem to a
  KItem.
- Added support for nested cells of multiplicity * in unification-based
  rewriter.
- Added support for `--superheat` and `--supercool`.
- Added support for rules tagged `function` which do not have a rewrite
  at the top.
- Added support for a `--trace` flag in the matching-based rewriter 
  which prints a list of applied rules.
- Added increased error logging when the rewriter fails with an error.
- `--search` now respects `--transition`.

## Verification ##
- Updated Z3 API to 4.3.2 beta build bb56885147e4.
- Added substantial additional support for verifying static specifications of
  programs using the `--prove` option, which takes a K file containing
  reachability rules to verify. Features include:
    - SMTLib support for various operations on bit vectors, integers, lists,
      floats, and booleans.
    - An "smt-lemma" attribute which translates a particular rule into
      an SMTLib lemma to be used during sat-solving.
    - A "lemma" attribute which treats a rule as a lemma during proving
      to be additionally verified.
    - Conversion from functions with an "smtlib" attribute to
      uninterpreted functions in SMTLib.
    - Support for arbitrary bit width of bit vectors variables 
      using "bitwidth" attribute and the new term attribute syntax.
    - Support for arbitrary precision and exponent range of floating point
      variables using "exponent" and "significand" attributes and the
      new term attribute syntax.
    - A "pattern" attribute which specifies an associative-commutative-aware
      configuration abstraction, such as a list or list segment data structure
      in a heap.
    - A `--smt_prelude` option to KRun which specifies a prelude to be prepended
      to SMT queries.
    - A `--z3-executable` flag to use a separate process for SMT when
      z3 crashes due to a bug.
    - A "trusted" attribute which specifies that a particular reachability
      rule should be assumed sound instead of being proven.
    - Options `--z3-cnstr-timeout` and `--z3-impl-timeout` to set the Z3 timeout
      for checking constraints and implications, respectively.
- Removed support for gappa: z3 now handles all the same functionality.

## Miscellaneous ##
- Added a friendly error message when the tool throws an uncaught exception:
  `Uncaught exception thrown of type ...`
  If you see this error message, please file a bug so that we can either
  add a better error message, or fix the functionality that caused the error.
    - Also added a flag --debug which provides developers with the original
      stack trace.
- Changed the name of the K temp directory to `.<ToolName>-<Date>-<UUID>`.
- Improved error logging in cases where exceptions are caught by K code.
- Converted the K tutorial to use the Java backend for execution instead
  of Maude.
- Removed a number of unused files from the repository.
- Moved the `editor-support` folder to the separate repository 
  [k-editor-support](https://github.com/kframework/k-editor-support).

## Bug fixes ##
- Fixed Github issues #543, #720, #738, #780, #781, #789, #800, #825, #850,
  #873, #902, #909, #924, #938, #941, #976, #985, #990, #995, #997, #1047,
  #1059, #1073, #1088, #1090, #1126, #1153, among many other fixes.


# K Framework 3.4 (released 2014-08-05) #

This version is a major release.

## General ##
- Discontinued compatibility with Java 6.
- New folder structure:
	- Moved `editor-support` to the top level;
	- Renamed `examples` to `samples`
	- Improved and completely reorganized the tutorial 
- Removed `cink` from examples. Cink is a separate repository now.
- The `documentation/to-be-processed.txt` file contains more information about 
new features.


## Language ##
- Use of `when` deprecated; using instead `requires`
(and `ensures` for proof post-conditions).
- Replaced (deprecated) `List{K}` by `KList` (Issue #200).
- Generalized strictness.
- Supporting reject patterns as tags.
- Extending cast functionality with :, ::, <:, :>, <:>.
- Moving the `Int`, `Float`, and `#String` declarations from SDF into K.
- Updated `syntax K ::=` into `syntax KItem ::=`.
- Renamed `==MInt` and `=/=MInt` to `eqMInt` and `neMInt`.
- Improved the K-defined substitution to deal with arbitrary computations
including `.K` and `~>` sequences.


## Editor support ##
- Added a new plugin for working with K definitions into IntelliJ Idea.

## Kompile ##
- Using JCommander to handle command line options:
	- breaks code which attempts to access "--" options with only one "-";
	- breaks code which attempts to specify arguments to a parameter 
with an "=" (except `-cFOO=bar`)
	- renames experimental options to begin with an `X`
	- some of the options were renamed. Please check usage.
- `kcheck` tool was removed
- Added `--no-prelude` option which skips the auto inclusion of predefined 
files/modules.
- Implemented support for environment variable `K_OPTS` to specify additional
Java virtual machine arguments (Issue #91).
- Changed kompile to use unique temp files.
- Added a new backend (`doc`) for documentation generation (experimental).
- Checking tags specified by options like `--transition` are actually used in
rules (Issue #207).
- Improved reporting of running times in the verbose output mode (Issue #169).
- Parsing:
	- block attributes now propagate to individual productions (Issue #186);
	- improved reporting of ambiguities (Issue #182);
	- improved handling of `?` variables (Issue #153);
	- improving location information for rules (Issues #73, #108);
	- Anonymous variables are not allowed on the RHS of rewrites;
	- Improved caching of rules to speedup re-compilation if no syntax changes.


## Krun ##
- Changed option `--output-mode` to `--output` with short-name `-o`.
- Improved reporting of running times in the verbose output mode (Issue #169).
- `--search` now accepts more then one token in the input stream (Issue #159).
- Allowing syntactic sorts in `--search` patterns (Issue #114)
- Search graph is computed by Maude and parsed by krun only if one of the
arguments `--graph`, `--debug`, or `--debug-gui` is set (Issue #37).
- Colors: Improved color matching algorithm for terminals. Now more cells
should be colored. Added a new krun option: `--terminal-color`, to specify the
background color of the terminal.
- Fixed LTL model checking for negative results (Issue #481).
- Graphical Debugger:
	- save/load configuration;
	- export graph as PNG;
	- improved diff frame;
	- improved duplicate detection for the `step-all` command.

## Kast ##
- Using JCommander to handle kast options
	- breaks code which attempts to access "--" options with only one "-";
	- some of the options were renamed. Please check usage.

## KTest ##
- Failing when pdf generation fails (Issue #683).
- Printing tested output file in case of match failure (Issue #689).
- Fixed error messages to contain an executable command (Issue #518).
- Fixed exception reporting (Issues #407, #485).
- Removing redundant messages for skipped steps (Issue #375).
- Fixed color output for non-ANSI terminals (Issue #368).
- Fixed exception thrown by `--timeout` option (Issue #223).
- Made `directory`, `programs` and `results` arguments
absolute paths (Issue #202).
- Show more precise timing information in ktest (Issue #193).
- Generate and update results automatically (Issue #133). New options:
 `--update-out`, `--generate-out`, `--dry-run`.
- Added `--threads` parameter.
- Added support for using environment variables in configuration files.
- Changed default value of `programs` and `results` options (Issue #99, #93).
- Added `--ignore-white-spaces` option.
- Support new feature: options `more-programs`, `more-results` (Issue #134).
- Multiple program and results directories supported (Issue #96).


## Java Backend ##
- Implementation for builtin string operations.
- Added tag `interface` for data structure update operations.
- Added option `--pattern-matching` to krun.
- Adding special `autoinclude-java.k` for the Java backend.
- Support for maps as cells.
- Added support for proving properties related to floats
(using the gappa prover).
- Partial Z3 model integration.

## Test Generation ##
- Option `--test-gen` added to kompile (experimental)
