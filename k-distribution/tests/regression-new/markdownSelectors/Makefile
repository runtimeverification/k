DEF=test
EXT=test
TESTDIR=.
KOMPILE_BACKEND=haskell
KOMPILE_FLAGS=--md-selector '(k|keep) & !discard'
KPROVE_FLAGS+=--md-selector k

include ../../../include/kframework/ktest.mak

KPROVE_OR_LEGACY=$(KPROVE)
CONSIDER_PROVER_ERRORS=2>&1
