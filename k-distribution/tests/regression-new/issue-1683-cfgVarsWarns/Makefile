DEF=test
EXT=test
TESTDIR=.
KOMPILE_FLAGS=--syntax-module TEST
KOMPILE_BACKEND=haskell
KRUN_FLAGS=-cA=.K

include ../../../include/kframework/ktest.mak
%.$(EXT): kompile
	$(KRUN_OR_KX) $@ $(KRUN_FLAGS) $(DEBUG) -d $(DEFDIR) $(CONSIDER_ERRORS) $(REMOVE_PATHS) $(CHECK) $@.out
