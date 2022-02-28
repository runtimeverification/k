DEF=test
EXT=
TESTDIR=.
KOMPILE_FLAGS+=--gen-glr-bison-parser

test: test.kore
	$(LLVM_KRUN) \
	  -d ./test-kompiled \
	  -c PGM test.kore KItem korefile \
	  | diff - test.out

test.kore: test.in kompile
	./test-kompiled/parser_PGM $< > $@

include ../../../include/kframework/ktest.mak

clean:
	rm -rf test.kore $(KOMPILED_DIR) .depend-tmp .depend .kompile-* .krun-* .kprove-* kore-exec.tar.gz
