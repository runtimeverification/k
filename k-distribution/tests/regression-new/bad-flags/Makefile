DEF=test
KOMPILE_BACKEND=llvm
KOMPILE_FLAGS=--syntax-module TEST

CHECK=2>&1 | diff -
ALLOW_FAIL=

.PHONY: all clean update-results
all:
	$(KOMPILE) $(CHECK) no-flags.out $(ALLOW_FAIL)
	$(KOMPILE) $(KOMPILE_FLAGS) --badflag --extra --backend $(KOMPILE_BACKEND) $(DEBUG) $(DEF).$(SOURCE_EXT) -d $(DEFDIR) $(CHECK) extra-flags.out $(ALLOW_FAIL)

include ../../../include/kframework/ktest.mak

update-results: CHECK=2>
update-results: ALLOW_FAIL=; true
