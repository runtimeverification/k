DEF=test
EXT=test
TESTDIR=.
KOMPILE_BACKEND=llvm
KOMPILE_FLAGS+=--gen-glr-bison-parser --llvm-proof-hint-instrumentation
KRUN_FLAGS=--proof-hint

include ../../../include/kframework/ktest.mak

clean:
	rm -rf out.hint test.kore $(KOMPILED_DIR) .depend-tmp .depend .kompile-* .krun-* .kprove-* kore-exec.tar.gz
