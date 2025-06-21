# klean

The `pyk.klean` module enables Lean 4 code generation from a kompiled KORE
definition.


## Command Line Interface

After installation of the `kframework` package, the code generator is available
on the command line under the `klean` command.

```
usage: klean [-h] [-o DIR] [-l NAME] [-r LABEL] [--derive-beq] [--derive-decidableeq] DEFN_DIR PKG_NAME

Generate a Lean 4 project from a K definition

positional arguments:
  DEFN_DIR              definition directory
  PKG_NAME              name of the generated Lean 4 package (in kebab-case)

options:
  -h, --help            show this help message and exit
  -o, --output DIR      output directory (default: .)
  -l, --library NAME    name of the generated Lean library (default: package name in PascalCase)
  -r, --rule LABEL      labels of rules to include (default: all)
  --derive-beq          derive BEq for all types
  --derive-decidableeq  derive DecidableEq for all types except SortKItem and its dependents
```

The `-r` flag can be provided multiple times, each time with a rule label, to
include only those rules (and their transitive dependencies) in the generated
output.


## Example

In the following, all example commands assume the following:
* Lean 4 is installed, `lake` is on `$PATH`.
* The K Framework is installed, the correct version of `kompile` is on `$PATH`.
* The `runtimeverification/k` repository is cloned, `$PWD` is the `pyk`
  directory.


```bash
$ kompile src/tests/integration/test-data/k-files/imp.k  # kompile the IMP definition
$ uv run klean imp-kompiled klean-imp                # generate the Lean 4 project
```

The command produces the following files:

```
$ tree klean-imp
klean-imp
├── KleanImp
│   ├── Func.lean
│   ├── Inj.lean
│   ├── Prelude.lean
│   ├── Rewrite.lean
│   └── Sorts.lean
├── KleanImp.lean
├── lakefile.toml
└── lean-toolchain
```

| File | Description |
| ---- | ----------- |
| `KleanImp.lean` | Main library file. |
| `KleanImp/Prelude.lean` | A prelude with basic declarations shared between all generated projects. |
| `KleanImp/Sorts.lean` | Type declarations for all relevant[^1] sorts in the K definition. |
| `KleanImp/Inj.lean` | A definition for the `inj` function based on the subsort relation using instances. |
| `KleanImp/Func.lean` | Axioms for all relevant[^1] function signatures in the K definition. |
| `KleanImp/Rewrite.lean` | A dependent type that encodes the rewrite relation over configurations[^2]. |

[^1]: With regards to the incuded rewrite rules.
[^2]: To be more precise, it encodes an over-approximation of the relation, as it does not take rule priorities into consideration.

The generated files constitute a `lake` project:

```toml
# klean-imp/lakefile.toml

name = "klean-imp"
version = "0.1.0"
defaultTargets = ["KleanImp"]
weakLeanArgs = [
    "-D maxHeartbeats=10000000"
]

[[lean_lib]]
name = "KleanImp"
```

The command `lake build` builds the project:

```
$ lake -d klean-imp build
info: klean-imp: no previous manifest, creating one from scratch
info: toolchain not updated; already up-to-date
Build completed successfully.
```
