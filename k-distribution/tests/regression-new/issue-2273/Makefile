DEF=a
EXT=a
KAST_FLAGS+=--sort Foo

include ../../../include/kframework/ktest.mak


%.kast: kompile
ifeq ($(TESTDIR),$(RESULTDIR))
	$(KAST) $@ $(KAST_FLAGS) $(DEBUG) -d $(DEFDIR) $(CONSIDER_ERRORS) $(REMOVE_PATHS) $(CHECK) $@.out
else
	$(KAST) $@ $(KAST_FLAGS) $(DEBUG) -d $(DEFDIR) $(CONSIDER_ERRORS) $(REMOVE_PATHS) $(CHECK) $(RESULTDIR)/$(notdir $@).out
endif
