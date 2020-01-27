DEF=demo
EXT=demo
TESTDIR=.
KOMPILE_BACKEND=java
KPROVE_FLAGS=--def-module VERIFICATION
CHECK= 2>&1 | diff -

export KOMPILE_BACKEND
export KPROVE_FLAGS
export CHECK

include ../../../include/ktest.mak
