DEF=test
EXT=test
TESTDIR=.
KOMPILE_FLAGS=--syntax-module TEST --gen-glr-bison-parser --bison-parser-library --llvm-kompile-type c --llvm-kompile-output libfoo

UNAME := $(shell uname)
ifeq ($(UNAME),Darwin)
	CC=clang
else
	CC=gcc
endif

check: test.kore
	diff test.kore test.out

test: kompile
	$(CC) test.c -Ltest-kompiled -lfoo -lparser_KItem_TEST -o test

test.kore: test test.in
	LD_LIBRARY_PATH=test-kompiled ./test test.in > test.kore

include ../include/ktest.mak

clean:
	rm -rf ./test-kompiled .depend-tmp .depend .kompile-* .krun-* .kprove-* .kbmc-* kore-exec.tar.gz
	rm -rf test.kore test
