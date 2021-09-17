DEF=test
EXT=test
KOMPILE_BACKEND=haskell
TESTDIR=.
KOMPILE_FLAGS=--profile-rule-parsing test-kompiled/timing.log --syntax-module TEST
KPROVE_FLAGS=--profile-rule-parsing test-kompiled/spectiming.log

include ../../../include/kframework/ktest.mak

KPROVE_OR_X=$(KPROVEX)
CONSIDER_PROVER_ERRORS=2>&1
