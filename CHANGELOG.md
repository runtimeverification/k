<!-- Copyright (c) 2014 K Team. All Rights Reserved. -->

# K Framework 3.5 #

## Kompile ##
- `kompile --backend [pdf|latex|html|unparse|unflatten|doc]` has been
  moved to a new tool, `kdoc --format [pdf|latex|html|unparse|unflatten|doc]`
- Modules are required to import or declare constructors for sorts that they
  use. In the event of a circularity, a forward reference can be introduced
  using the syntax `syntax Sort` without any declared productions.

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
