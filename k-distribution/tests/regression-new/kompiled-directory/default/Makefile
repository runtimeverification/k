DEF=test
EXT=test
TESTDIR=.
KOMPILE_FLAGS+=--syntax-module TEST
KOMPILE_BACKEND=llvm

include ../../../../include/kframework/ktest.mak

CHECK := $(REMOVE_PATHS) $(CHECK)
update-results: CHECK := $(REMOVE_PATHS) $(CHECK)
