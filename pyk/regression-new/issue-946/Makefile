DEF=test
EXT=test
KOMPILE_FLAGS=--syntax-module TEST

include ../include/ktest.mak
krun: kompile
	$(KRUN_OR_LEGACY) $(KRUN_FLAGS) $(DEBUG) --definition $(DEF)-kompiled $(CHECK) output
