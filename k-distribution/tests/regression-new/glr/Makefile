DEF=test
EXT=foo
TESTDIR=.
KOMPILE_FLAGS+=--gen-glr-bison-parser

test: test.kore
	$(KPRINT) test-kompiled test.kore | diff - test.ref

test.kore: 1.test kompile
	./test-kompiled/parser_PGM 1.test > test.kore
include ../../../include/kframework/ktest.mak

clean:
	rm -rf test.kore test-kompiled


KRUN=./parse
