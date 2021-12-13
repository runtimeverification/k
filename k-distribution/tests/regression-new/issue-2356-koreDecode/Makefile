DEF=test
EXT=test
TESTDIR=.
KOMPILE_BACKEND=haskell
KAST_FLAGS=-i kore -o pretty

include ../../../include/kframework/ktest.mak

result2.kore.kast: kompile
	${K_BIN}/kore-print result.kore.kast $(CHECK) result.kore.kast.out
