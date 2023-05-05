DEF=iele
EXT=
TESTDIR=.

test: test.kore
	cat test.kore | diff - test.ref

test.kore: forwarder.iele kompile
	./iele-kompiled/parser_PGM forwarder.iele > test.kore
include ../../../include/kframework/ktest.mak

clean:
	rm -rf test.kore $(KOMPILED_DIR) .depend-tmp .depend .kompile-* .krun-* .kprove-* kore-exec.tar.gz


KRUN_OR_KX=./parse
