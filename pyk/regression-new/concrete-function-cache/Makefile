DEF=a
TESTDIR=.
EXT=a
KOMPILE_BACKEND=haskell
KOMPILE_FLAGS=

%-spec.k %-spec.md: kompile
ifeq ($(TESTDIR),$(RESULTDIR))
	$(KPROVE) $@ $(KPROVE_FLAGS) $(DEBUG) $(CONSIDER_ERRORS) $(REMOVE_PATHS) | sed 's!kore-exec: \[[0-9]*\]!kore-exec: []!g' $(CHECK) $@.out
else
	$(KPROVE) $@ $(KPROVE_FLAGS) $(DEBUG) $(CONSIDER_ERRORS) $(REMOVE_PATHS) | sed 's!kore-exec: \[[0-9]*\]!kore-exec: []!g' $(CHECK) $(RESULTDIR)/$(notdir $@).out
endif

include ../include/ktest.mak

CONSIDER_PROVER_ERRORS=2>&1
