DEF=test
EXT=test
KOMPILE_FLAGS=--syntax-module TEST

include ../include/ktest.mak
krun: kompile
	$(KRUN) $(KRUN_FLAGS) $(DEBUG) --definition $(DEF)-kompiled $(CHECK) output
