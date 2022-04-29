DEF=proofSyntax
TESTDIR=.
KOMPILE_BACKEND=haskell
KPROVE_FLAGS=-m VERIFICATION

%-spec.k %-spec.md: kompile
ifeq ($(TESTDIR),$(RESULTDIR))
	$(KPROVE_LEGACY) $@ $(KPROVE_FLAGS) $(DEBUG) -d $(DEFDIR) $(CONSIDER_ERRORS) $(REMOVE_PATHS) | sed 's!kore-exec: \[[0-9]*\]!kore-exec: []!g' $(CHECK) $@.out
else
	$(KPROVE_LEGACY) $@ $(KPROVE_FLAGS) $(DEBUG) -d $(DEFDIR) $(CONSIDER_ERRORS) $(REMOVE_PATHS) | sed 's!kore-exec: \[[0-9]*\]!kore-exec: []!g' $(CHECK) $(RESULTDIR)/$(notdir $@).out
endif

include ../../../include/kframework/ktest.mak
