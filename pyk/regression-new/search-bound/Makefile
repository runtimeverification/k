DEF=test
EXT=test
TESTDIR=.
KOMPILE_BACKEND=llvm
KOMPILE_FLAGS=--enable-search  --syntax-module TEST
KRUN_FLAGS=--search --bound ${BOUND} --depth 2

1.test: BOUND=0
2.test: BOUND=1
3.test: BOUND=2

include ../include/ktest.mak
