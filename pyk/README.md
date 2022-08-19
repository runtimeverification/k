# pyk


## Installation

Prerequsites: `python 3.8.*`, `pip >= 20.0.2`.

```bash
pip install git+https://github.com/runtimeverification/k.git[@<ref>]#subdirectory=pyk
```

## For Developers

Prerequsite: `poetry >= 1.1.4`.

Use `make` to run common tasks (see the [Makefile](Makefile) for a complete list of available targets).

* `make check`: check code style
* `make format`: format code
* `make test-unit`: run unit tests
* `make test-integration`: run integration tests

For interactive use, spawn a shell with `poetry shell` (after `poetry install`), then run an interpreter.
