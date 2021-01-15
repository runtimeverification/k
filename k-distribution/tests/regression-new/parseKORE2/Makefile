DEF=test
EXT=test
KOMPILE_FLAGS=--syntax-module TEST

include ../../../include/kframework/ktest.mak
krun: kompile
	$(KRUN_OR_KX) $(KRUN_FLAGS) $(DEBUG) -d $(DEFDIR) $(CHECK) output
