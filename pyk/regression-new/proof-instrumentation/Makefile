DEF=test
KOMPILE_BACKEND=llvm
KOMPILE_FLAGS+=--gen-glr-bison-parser --llvm-proof-hint-instrumentation
LLVM_KRUN_FLAGS=-d ./test-kompiled --proof-hints

check: out.hint
	head -c4 out.hint | diff - <(echo -n 'HINT')

out.hint: test.kore
	rm -f $@
	$(LLVM_KRUN) $(LLVM_KRUN_FLAGS) \
		-c PGM $< Foo korefile -o $@

test.kore: test.in kompile
	./test-kompiled/parser_PGM $< > $@

include ../include/ktest.mak

clean:
	rm -rf out.hint test.kore $(KOMPILED_DIR) .depend-tmp .depend .kompile-* .krun-* .kprove-* kore-exec.tar.gz

update-results: CHECK=> test.out
