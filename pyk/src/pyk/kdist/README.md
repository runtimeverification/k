# kdist

The `kdist` module uses the Python entry point mechanism to make build targets
available through a command line interface. In the following, we demonstrate
the use of the module on a simple example.


## Create a new Python project

We'll use `uv` for managing dependencies, but the approach works with any
build tool that supports entry points (in particular, with any
[PEP 621](https://peps.python.org/pep-0621/) compilant build back-end).

```
imp-semantics
├── uv.lock
├── pyproject.toml
└── src
    └── imp_semantics
        └── __init__.py
```

`pyproject.toml`:

```toml
[build-system]
requires = ["hatchling"]
build-backend = "hatchling.build"

[project]
name = "imp-semantics"
version = "0.1.0"
description = "K semantics for a simple imperative programing language"
readme = "README.md"
requires-python = "~=3.10"
dependencies = [
    "kframework",
]

[[project.authors]]
name = "Runtime Verification, Inc."
email = "contact@runtimeverification.com"
```

Notice that `kframework` is given as a dependency for the project. This setup
already gives us access to the `kdist` command:

```
$ uv run kdist list
```

Run `kdist --help` for the complete list of commands.


## Create a `kdist` plugin

```
imp-semantics
└── src
    └── imp_semantics
        └── kdist
            ├── __init__.py
            ├── imp.k
            └── plugin.py
```

Add an entry point to `pyproject.toml` for `imp-semantics.kdist.plugin`:

```toml
[project.entry-points.kdist]
imp-semantics = "imp_semantics.kdist.plugin"
```


## Define a build target

Let's verify the current setup by running `kdist list` again:

```
$ uv run kdist list
WARNING 2024-01-08 10:56:04,971 pyk.kdist._cache - Module does not define __TARGETS__: imp_semantics.kdist.plugin
```

The warning already hints on the particular module structure `kdist` expects.
Let's add the `__TARGETS__` attribute to fix the warning.

```python3
__TARGETS__ = {}
```

Next, let's populate the dictionary to expose build targets. For that, we need
to extend class `Target` from [api.py](api.py):

```python3
from collections.abc import Mapping
from pathlib import Path
from typing import Any, Final

from pyk.kdist.api import Target
from pyk.ktool.kompile import kompile


MAIN_FILE: Final = Path(__file__).parent / 'imp.k'


class ImpTarget(Target):
    args: dict[str, Any]

    def __init__(self, args: Mapping[str, Any]):
        self.args = dict(args)

    def build(self, output_dir: Path, deps: dict[str, Path], args: dict[str, Any], verbose: bool) -> None:
        kompile(
            output_dir=output_dir,
            verbose=verbose,
            main_file=MAIN_FILE,
            **self.args
        )


__TARGETS__: Final = {
    'llvm': ImpTarget({'backend': 'llvm'}),
    'haskell': ImpTarget({'backend': 'haskell'}),
}
```

Command `kbuild list` now lists our build targets:

```
$ uv run kdist list
imp-semantics
* llvm
* haskell
```


## Build targets

```
$ uv run kdist --verbose build -j2
INFO 2024-01-08 12:18:04,651 pyk.kdist._cache - Loading target cache
INFO 2024-01-08 12:18:04,663 pyk.kdist._cache - Loading plugin: imp-semantics
INFO 2024-01-08 12:18:04,663 pyk.kdist._cache - Importing module: imp_semantics.kdist.plugin
INFO 2024-01-08 12:18:04,668 pyk.kdist._cache - Target cache loaded in 0.017s
INFO 2024-01-08 12:18:04,668 pyk.kdist._kdist - Building targets: imp-semantics.haskell, imp-semantics.llvm
INFO 2024-01-08 12:18:04,674 pyk.ktool.kompile - Running: kompile <path-to-imp-semantics>/src/imp_semantics/kdist/imp.k --emit-json --backend haskell --output-definition /home/<user>/.cache/kdist-<digest>/imp-semantics/haskell --verbose
INFO 2024-01-08 12:18:04,675 pyk.ktool.kompile - Running: kompile <path-to-imp-semantics>/src/imp_semantics/kdist/imp.k --emit-json --backend llvm --output-definition /home/<user>/.cache/kdist-<digest>/imp-semantics/llvm --verbose
...
```

Inspect the output:

```
$ uv run kdist which
/home/<user>/.cache/kdist-<digest>
```

```
/home/<user>/.cache/kdist-<digest>
└── imp-semantics
    ├── haskell
    ├── haskell.json
    ├── llvm
    └── llvm.json
```
