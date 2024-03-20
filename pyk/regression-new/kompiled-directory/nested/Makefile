DEF=test
EXT=test
TESTDIR=.
KOMPILE_BACKEND=llvm
KOMPILE_FLAGS+=--syntax-module TEST
DEFDIR=some/nested/path

include ../../include/ktest.mak

CHECK := $(REMOVE_PATHS) $(CHECK)
update-results: CHECK := $(REMOVE_PATHS) $(CHECK)

clean:
	rm -rf $(KOMPILED_DIR) .depend-tmp .depend .kompile-* .krun-* .kprove-* kore-exec.tar.gz
	cd some/nested/path && rm -rf $(KOMPILED_DIR) .depend-tmp .depend .kompile-* .krun-* .kprove-* kore-exec.tar.gz || true
