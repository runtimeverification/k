DEF=a
EXT=a
KAST_FLAGS+=--sort Foo --no-exc-wrap

include ../include/ktest.mak


%.kast: kompile
ifeq ($(TESTDIR),$(RESULTDIR))
	$(KAST) $@ $(KAST_FLAGS) $(DEBUG) --definition $(DEF)-kompiled $(CONSIDER_ERRORS) $(REMOVE_PATHS) $(CHECK) $@.out
else
	$(KAST) $@ $(KAST_FLAGS) $(DEBUG) --definition $(DEF)-kompiled $(CONSIDER_ERRORS) $(REMOVE_PATHS) $(CHECK) $(RESULTDIR)/$(notdir $@).out
endif
