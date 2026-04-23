# pyk/regression-new — Skipped Test Triage

This document categorises the 113 skipped tests in `pyk/regression-new/skipped` by root cause,
lists the tests in each category, and identifies quick-win opportunities.

## Category A — Haskell backend (≈39 tests)

These tests set `KOMPILE_BACKEND=haskell`.
They require the Haskell symbolic execution backend which is not the primary focus of the pyk test suite.

```
cell-sort-haskell, checkClaimError, concrete-function, concrete-function-cache,
concrete-haskell, context-alias-2, context-labels, domains-lemmas-no-smt,
imp-haskell, issue-1175, issue-1436, issue-1489-claimLoc, issue-1676-koreBytes,
issue-1682-korePrettyPrint, issue-1683-cfgVarsWarns, issue-2142-markConcrete,
issue-2174-kprovexParseError, issue-2287-simpl-rules-in-kprovex,
issue-2321-kprovexCrash, issue-2356-koreDecode, ite-bug, kast-kore-input,
kprove-append, kprove-branchingAllowed, kprove-error-status, kprove-java,
kprove-markdown, kprove-var-equals, map-symbolic-tests-haskell, markdownSelectors,
or-haskell, poly-sort, poly-unparsing, profile, quadratic-poly-unparsing,
set-symbolic-tests, set_unification, spec-rule-application, unification-lemmas
```

Not addressable without Haskell backend support.

## Category B — GLR / Bison parser generation (≈16 tests)

These tests pass `--gen-glr-bison-parser` or `--gen-bison-parser` to `kompile`.
They require C compilation and bison integration that is not available in pyk.

```
bison-parser-library, glr, glr2, glr3, glr4, imp++-llvm, issue-1602,
kast-bison, kast-bison-bytes, llvm-krun, locations, locations2, locations3,
parse-c, parseNonPgm, proof-instrumentation
```

Not addressable without bison integration.

## Category C — kore backend (4 tests)

These tests use `KOMPILE_BACKEND=kore` (the bytecode interpreter backend).

```
fresh1, fresh2, imp-kore, kore-brackets
```

Not addressable without kore backend support.

## Category D — `pyk parse` subcommand missing (≈10 tests)

The `ktest.mak` infrastructure sets `KAST=$(UV_RUN) pyk parse`, but `pyk parse` is not a
valid subcommand in the current pyk CLI (valid commands: print, rpc-print, rpc-kast,
prove-legacy, kompile, kompilex, run, prove, show, graph-imports, coverage,
kore-to-json, json-to-kore, parse-outer).

These tests exercise the KAST parsing / pretty-printing pipeline.

```
equals-formatting, issue-2273, issue-3647-debugTokens, issue-3672-debugParse,
json-input, kast-default-output, kast-input, kast-rule
```

Also: `issue-1088` (uses `KAST_FLAGS=--output kast --output-file`).

**Fix**: Add a `pyk parse` (or `pyk kast`) CLI subcommand that wraps the Java `kast` binary
(similar to how `pyk kompile` wraps `kompile`), or wire pyk's inner-parsing infrastructure
into a CLI command.

## Category E — Missing `pyk run` flags

`pyk run` (`exec_run` in `__main__.py`) is a thin wrapper that only accepts `pgm_file` and
`--definition`.
Several tests require flags that pass-through to the underlying Java `krun`:

- `-cVAR=VALUE` (cell configuration override): `doubleinj`
- `--output program`: `issue-1145`
- `--parser <script>`: `issue-582`, `star-multiplicity`
- `--search`, `--search-final`, `--no-pattern`, `--bound`, `--depth`: `context-alias-2`,
  `no-pattern`, `search-bound`, `issue-3520-freshConfig`
- `--io off`: `issue-1436` (also haskell)
- `--output kore`: `issue-1676-koreBytes` (also haskell)

**Fix**: Extend `pyk run` to pass unrecognised flags through to the underlying `krun` binary,
or map the common ones explicitly.

## Category F — Missing `pyk kompile` flags

`pyk kompile` doesn't expose all Java `kompile` flags:

- `--top-cell`: `issue-2075-2`
- `--profile-rule-parsing`: `profile` (also haskell)
- `--llvm-proof-hint-instrumentation`: `proof-instrumentation` (also bison)
- `--llvm-kompile-type library`: `llvm-kompile-type`

**Fix**: Add these as pass-through or explicit options in `pyk kompile`.

## Category G — `<generatedCounter>` cell shown in output (≈6+ tests)

Java `krun` strips the synthetic `<generatedCounter>` cell from output.
`pyk run` (`KRun.pretty_print`) does not strip it.
Tests whose K definitions use `generatedCounter` produce output that differs from baseline.

Observed in: `context-alias`, `issue-1263`, `issue-1528`, `or-llvm`, `rand`, `rangemap-tests-llvm`
(possibly more — not all tests were run).

**Fix**: Strip `<generatedCounter>` from `KRun.pretty_print` output, matching Java `krun` behaviour.
Then regenerate `.out` baselines with `make update-results`.

## Category H — Output format differences

Some tests have `.out` baselines that predate the current pyk pretty-printer formatting.
These are likely fixable by running `make update-results` after verifying the actual output
is correct.

Observed patterns:
- Inline collection items vs. one-per-line (e.g. `rand`: `ListItem(1) ListItem(2)` vs.
  `ListItem(1)\nListItem(2)`)
- Different argument ordering in error messages (e.g. `checks`)
- Extra `[ERROR] Running process failed...` line in `pyk kompile` failure messages
  (e.g. `nonexhaustive`) — not emitted by Java `kompile`

## Category I — Special tool dependencies

Tests that require infrastructure beyond pyk's CLI:

- `append`: requires custom `./kparse-twice` script
- `bad-flags`: tests `kompile --badflag` error output (argument-order mismatch in baseline)
- `help`: tests `--help` and `--version` output for many K tools (`kserver`, `kparse-gen`, etc.)
- `io-llvm`: requires `./prepare.sh` script
- `issue-582`, `star-multiplicity`: require `./test-parser` script
- `issue-946`: calls `pyk run` without a `pgm_file` (uses `--definition` only — not supported)
- `issue-1169`: uses `kompile -E` (preprocessor mode)
- `issue-1844-noPGM`, `issue-2812-kprove-filter-claims`, `issue-2909-allow-anywhere-haskell`,
  `itp`, `kdep-options`, `mutable-bytes`, `non-executable`, `pl-tutorial`, `proof-tests`,
  `rat`, `boundary-cells-opt`: group tests (SUBDIRS) — skip reason inherited from sub-tests

## Category J — Likely quick wins not yet investigated

These look like standard LLVM tests with no obviously missing features but have not been
run yet:

```
configuration-formatting (output format diff — generatedTop)
doubleinj (needs -c flag in pyk run)
issue-1098 (no special flags — needs running)
issue-2273 (kast, needs pyk parse)
pattern-macro (output format diff — generatedTop)
pattern-macro-productions (similar)
```

## Summary Table

| Category | Count | Fix complexity |
|----------|-------|---------------|
| A — Haskell backend | ~39 | High (needs Haskell) |
| B — GLR/Bison | ~16 | High (needs C bison) |
| C — kore backend | 4 | Medium |
| D — `pyk parse` missing | ~10 | Medium (add CLI command) |
| E — Missing `pyk run` flags | ~8 | Low–Medium (pass-through flags) |
| F — Missing `pyk kompile` flags | ~4 | Low (add flags) |
| G — `<generatedCounter>` stripping | ~6+ | Low (strip in pretty_print) |
| H — Output format differences | ~5 | Low (update-results) |
| I — Special tool deps | ~15 | Varies |

**Recommended priority**: G → E → D → F → H, then revisit per-test
