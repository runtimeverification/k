DEF=a
EXT=a
KOMPILE_BACKEND=haskell
TESTDIR=.
KOMPILE_FLAGS=--concrete-rules "A.f1"

%-spec.k %-spec.md: kompile
ifeq ($(TESTDIR),$(RESULTDIR))
	$(KPROVE) $@ $(KPROVE_FLAGS) $(DEBUG) --definition $(DEF)-kompiled $(CONSIDER_ERRORS) $(REMOVE_PATHS) | sed 's!kore-exec: \[[0-9]*\]!kore-exec: []!g' $(CHECK) $@.out
else
	$(KPROVE) $@ $(KPROVE_FLAGS) $(DEBUG) --definition $(DEF)-kompiled $(CONSIDER_ERRORS) $(REMOVE_PATHS) | sed 's!kore-exec: \[[0-9]*\]!kore-exec: []!g' $(CHECK) $(RESULTDIR)/$(notdir $@).out
endif

include ../include/ktest.mak

CONSIDER_PROVER_ERRORS=2>&1
