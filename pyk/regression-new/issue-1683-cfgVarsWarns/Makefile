DEF=test
EXT=test
TESTDIR=.
KOMPILE_FLAGS=--syntax-module TEST
KOMPILE_BACKEND=haskell
KRUN_FLAGS=-cA=.K

include ../include/ktest.mak
%.$(EXT): kompile
	$(KRUN) $@ $(KRUN_FLAGS) $(DEBUG) --definition $(DEF)-kompiled $(CONSIDER_ERRORS) $(REMOVE_PATHS) $(CHECK) $@.out
