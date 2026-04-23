copyright: Copyright (c) Runtime Verification, Inc. All Rights Reserved.

# K Framework — Agent Guide

## Project Overview

The K Framework is a language-agnostic formal specification and verification framework developed by Runtime Verification.
It lets you define programming language semantics in `.k` files and then automatically derives an interpreter, model checker, and deductive verifier from that definition.

The repository is a monorepo with two independent technology stacks:

- **Java/Scala** — the K compiler toolchain (`kompile`, `krun`, `kprove`, etc.)
- **Python** (`pyk/`) — the `kframework` Python SDK for programmatically interacting with the K toolchain

## Repository Structure

```
k-frontend/                  K language parser and frontend (Java/Scala)
k-distribution/              Main distribution bundle
  bin/, lib/                   Symlinks into target/release/k/
  include/kframework/          Shared Makefile infrastructure (ktest.mak, ktest-group.mak)
  tests/regression-new/        Java-backend regression suite (229 test subdirs)
haskell-backend/             Haskell-based symbolic backend
llvm-backend/                LLVM-based concrete execution backend
pyk/                         Python SDK sub-project (self-contained)
  src/pyk/                     Package source (cli, kast, kore, proof, kcfg, kdist, …)
  src/tests/                   pytest test suite (unit/, integration/)
  regression-new/              Python-backend regression suite (213 test subdirs)
  pyproject.toml               Build & tool config (hatchling, black, mypy, flake8, …)
  Makefile                     All pyk make targets
k-tutorial/                  Tutorial K definitions
```

## Build

### Java (compile only, skip tests)

```
mvn package -DskipTests
```

This compiles all Maven modules (`k-frontend`, `k-distribution`, `haskell-backend`, `llvm-backend`) and produces JARs under each module's `target/` directory.
Java 17 and Scala 2.13 are required.

### Python

The `pyk/` sub-project uses `hatchling` as its build backend and `uv` as its package manager.
No explicit build step is needed before running lint or tests — the make targets handle installation.

## Lint

Python only (there is no lint target for Java):

```
make -C pyk check
```

This runs, in order: `black --check`, `isort --check`, `autoflake --check`, `flake8`, `mypy`, `pydocstyle`.

To auto-apply all formatters:

```
make -C pyk format
```

Key style settings (from `pyk/pyproject.toml`):
- `black`: line-length 120, skip-string-normalization
- `isort`: black profile, line-length 120
- `mypy`: `disallow_untyped_defs = true`
- `pydocstyle`: Google convention

## Tests

There are four distinct test surfaces.

### 1. Java unit tests

```
mvn verify
```

Runs all JUnit 4 tests across `k-frontend` and `k-distribution` via Maven Surefire.
Tests run with `LC_NUMERIC=en_US.UTF-8`.

### 2. Python unit + integration tests

```
make -C pyk test
```

Runs `src/tests/unit/` and `src/tests/integration/` with 4 parallel workers (pytest-xdist, worksteal).
Unit tests only (faster, no K toolchain required):

```
make -C pyk test-unit
```

### 3. Java regression tests

```
make -C k-distribution/tests/regression-new
```

229 subdirectory test cases.
Each test compiles a `.k` definition with `kompile` and executes it with `krun` or `kprove`, comparing output against `.out` baseline files.
The shared test infrastructure lives in `k-distribution/include/kframework/ktest.mak`.

### 4. Python regression tests

```
make -C pyk/regression-new
```

213 subdirectory test cases; 113 are currently skipped (listed in `pyk/regression-new/skipped`).
Same test infrastructure as the Java regression suite but exercises pyk-specific code paths.

## Updating Regression Baselines

If a change intentionally alters K program output, regenerate the `.out` files:

```
make -C k-distribution/tests/regression-new update-results
make -C pyk/regression-new update-results
```

Commit the updated baseline files in a dedicated commit after the logic change.
