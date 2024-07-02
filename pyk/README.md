# pyk

[API documentation](https://kframework.org/pyk/)


## Installation

```bash
pip install kframework
```


## For Developers

Prerequsites: `python >= 3.10`, `poetry >= 1.3.2`.

Use `make` to run common tasks
(see the [Makefile](https://github.com/runtimeverification/k/blob/master/pyk/Makefile)
for a complete list of available targets).

* `make build`: Build wheel
* `make check`: Check code style
* `make format`: Format code
* `make test-unit`: Run unit tests
* `make test-integration`: Run integration tests

For interactive use, spawn a shell with `poetry shell` (after `poetry install`), then run an interpreter.
