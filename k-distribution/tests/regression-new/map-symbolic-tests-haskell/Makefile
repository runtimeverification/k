# There are too many memory-intensive tests to run in parallel.
.NOTPARALLEL:

DEF=map-tests
EXT=mtest
TESTDIR=.
KOMPILE_BACKEND=haskell
KPROVE_FLAGS=--warnings none
export KORE_EXEC_OPTS=--log-level error

include ../../../include/kframework/ktest.mak
