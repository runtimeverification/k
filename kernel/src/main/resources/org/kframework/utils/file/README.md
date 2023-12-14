---
copyright: Copyright (c) Runtime Verification, Inc. All Rights Reserved.
---

Description of files contained in the `-kompiled` directory.
While most files are binaries, some are user readable and contain useful debugging information.
Most notably `parsed.txt` and `compiled.txt`.

Some temporary files can also be inspected by running the tools with `--debug`, `--temp-dir <dir>`
or `--save-temps`. Users are encouraged to use the PYK library to efficiently interact with these
files.

List of files:
- `parsed.txt` - user readable definition as seen by kompile immediately after parsing.
- `compiled.txt` - user readable definition after all the kompile steps have been applied. Variable
  renaming, configuration concretization, macro expansion, extra sorts and rules... This is
  what the backend will take as input.
- `parsed.json`, `compiled.json` - same as above but as JSON. Useful for loading into pyk.
  Generated when `--emit-json` is provided.
- `definition.kore` - the actual input for the backends - a close reflection of compiled.txt
- helper files for the scripts:
  - `backend.txt` - the backend used to kompile: haskell|llvm
  - `mainModule.txt` - main module name
  - `mainSyntaxModule.txt` - main syntax module name
  - `allRules.txt` - a hash list for all the rules
  - `configVars.sh` - the list of configuration variables, used by krun to initialize the config
  - `macros.kore` - macros to apply after parsing
- `cache.bin` - parsing cache. A mapping from bubble to the AST returned by the parser. On
  subsequent kompile calls only the newly modified rules will be parsed. This is the main file
  used by the KLSP to find occurrences and go to definition.
- `compiled.bin` - the entire definition as a binary dump from Java. Used by `kprove`.
- `scanner` - the tokenizer used by the parser.
- `timestamp` -  used by make to determine if it needs to rekompile.
- `haskellDefintion.bin` - haskell backend only. Binary format of definition.kore for efficient
  loading in the backend.
- `interpreter` - llvm backend only. Executable called by krun for concrete execution.
- `dt` folder - llvm temporary files to calculate the decision tree fast matching algorithm.
- `kore-exec.tar.gz` - archive with the input of the haskell backend in case it crashes. Useful
  for submitting bug reports.

Note 1: right now, we need to kompile the definition separately for each backend because the
compilation pipeline is very rigid. The differences between the backends start right from the very
first step, choosing what modules to include. That affects the syntax/functions/hooks available
in your definition, and mixing those can cause the backends to crash or, worse, give unsound
results.

Note 2: the content and the format of these files are subject to change without warning and they
should not be relied on for automation outside of what is already tested on CI.
