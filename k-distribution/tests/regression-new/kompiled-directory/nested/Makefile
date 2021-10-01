DEF=test
EXT=test
TESTDIR=.
KOMPILE_BACKEND=llvm
DEFDIR=some/nested/path

include ../../../../include/kframework/ktest.mak

CHECK := $(REMOVE_PATHS) $(CHECK)

clean:
	rm -rf $(KOMPILED_DIR) .depend-tmp .depend .kompile-* .krun-* .kprove-* .kbmc-* kore-exec.tar.gz
	cd some/nested/path && rm -rf $(KOMPILED_DIR) .depend-tmp .depend .kompile-* .krun-* .kprove-* .kbmc-* kore-exec.tar.gz || true
