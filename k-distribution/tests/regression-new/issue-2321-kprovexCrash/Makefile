DEF=test
TESTDIR=.
KOMPILE_BACKEND=haskell
KOMPILE_FLAGS=--syntax-module TEST --concrete-rules SERIALIZATION.keccak
export KORE_EXEC_OPTS=--log-level error

include ../../../include/kframework/ktest.mak

KPROVE_OR_LEGACY=$(KPROVE)
CONSIDER_PROVER_ERRORS=2>&1
