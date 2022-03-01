DEF=test
EXT=test
TESTDIR=.
KOMPILE_BACKEND=llvm
KOMPILE_FLAGS+=--gen-glr-bison-parser

CHECK=| diff - test.out
LLVM_KRUN_FLAGS=-p -d ./test-kompiled

1.test: korefile kore prettyfile pretty
	@:

korefile: test.kore
	$(LLVM_KRUN) $(LLVM_KRUN_FLAGS) \
	  -c PGM $< Foo korefile $(CHECK)

kore: test.kore
	$(LLVM_KRUN) $(LLVM_KRUN_FLAGS) \
	  -c PGM "$$(cat $<)" Foo kore $(CHECK)

prettyfile: test.in kompile
	$(LLVM_KRUN) $(LLVM_KRUN_FLAGS) \
	  -c PGM $< Foo prettyfile $(CHECK)

pretty: test.in kompile
	$(LLVM_KRUN) $(LLVM_KRUN_FLAGS) \
	  -c PGM "$$(cat $<)" Foo pretty $(CHECK)

test.kore: test.in kompile
	./test-kompiled/parser_PGM $< > $@

include ../../../include/kframework/ktest.mak

clean:
	rm -rf test.kore $(KOMPILED_DIR) .depend-tmp .depend .kompile-* .krun-* .kprove-* kore-exec.tar.gz
