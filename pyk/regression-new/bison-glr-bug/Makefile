DEF=iele
EXT=
TESTDIR=.
KOMPILE_FLAGS+=--gen-glr-bison-parser

test: test.kore
	cat test.kore | diff - test.ref

test.kore: forwarder.iele kompile
	./iele-kompiled/parser_PGM forwarder.iele > test.kore
include ../include/ktest.mak

clean:
	rm -rf test.kore $(KOMPILED_DIR) .depend-tmp .depend .kompile-* .krun-* .kprove-* kore-exec.tar.gz


KRUN_OR_KX=./parse
