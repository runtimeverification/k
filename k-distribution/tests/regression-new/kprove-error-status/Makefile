DEF=verif
EXT=verif
TESTDIR=.
KOMPILE_BACKEND=haskell

include ../../../include/kframework/ktest.mak

KPROVE_OR_LEGACY=$(KPROVE)
CONSIDER_PROVER_ERRORS=2>&1 | sed 's/\(kore-exec: \)\[[0-9]\+\]/\1/g' | sed 's/\(error, called at\) .*\.hs:[0-9]\+:[0-9]\+ in .*/\1/g'
