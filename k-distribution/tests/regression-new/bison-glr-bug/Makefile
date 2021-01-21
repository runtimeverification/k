DEF=iele
EXT=
TESTDIR=.
KOMPILE_FLAGS+=--gen-glr-bison-parser

test: test.kore
	cat test.kore | diff - test.ref

test.kore: forwarder.iele kompile
	./iele-kompiled/parser_PGM forwarder.iele > test.kore
include ../../../include/kframework/ktest.mak

clean:
	rm -rf test.kore test-kompiled .depend-tmp .depend .krun-*


KRUN_OR_KX=./parse
