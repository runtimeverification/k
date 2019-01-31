# path to the current makefile
MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
# path to the kompile binary of this distribuition
KOMPILE=$(abspath $(MAKEFILE_PATH)/../bin/kompile)
# ditto for krun
KRUN=$(abspath $(MAKEFILE_PATH)/../bin/krun)
# and kdep
KDEP=$(abspath $(MAKEFILE_PATH)/../bin/kdep)
# and kprove
KPROVE=$(abspath $(MAKEFILE_PATH)/../bin/kprove)
# path relative to current definition of test programs
TESTDIR?=tests
# path to put -kompiled directory in
DEFDIR?=.
# path relative to current definition of output/input files
RESULTDIR?=$(TESTDIR)
# all tests in test directory with matching file extension
TESTS?=$(wildcard $(TESTDIR)/*.$(EXT))
PROOF_TESTS?=$(wildcard $(TESTDIR)/*-spec.k)
# default KOMPILE_BACKEND
KOMPILE_BACKEND?=ocaml

CHECK=| diff -

.PHONY: kompile krun all clean update-results proofs

# run all tests
all: kompile krun proofs

# run only kompile
kompile: $(DEFDIR)/$(DEF)-kompiled/timestamp

$(DEFDIR)/%-kompiled/timestamp: %.k
	$(KOMPILE) $(KOMPILE_FLAGS) --backend $(KOMPILE_BACKEND) $(DEBUG) $< -d $(DEFDIR)
krun: $(TESTS)

proofs: $(PROOF_TESTS)

# run all tests and regenerate output files
update-results: krun proofs
update-results: CHECK=>

# run a single test. older versions of make run pattern rules in order, so
# if some programs should be run with different options their rule should be
# specified in the makefile prior to including ktest.mak.
%.$(EXT): kompile
ifeq ($(TESTDIR),$(RESULTDIR))
	cat $@.in 2>/dev/null | $(KRUN) $@ $(KRUN_FLAGS) $(DEBUG) -d $(DEFDIR) $(CHECK) $@.out
else
	cat $(RESULTDIR)/$(notdir $@).in 2>/dev/null | $(KRUN) $@ $(KRUN_FLAGS) $(DEBUG) -d $(DEFDIR) $(CHECK) $(RESULTDIR)/$(notdir $@).out
endif

%-spec.k: kompile
	$(KPROVE) $(KPROVE_FLAGS) -d $(DEFDIR) $@ $(CHECK) $@.out

clean:
	rm -rf $(DEFDIR)/$(DEF)-kompiled

.depend:
	@$(KDEP) $(DEF).k > .depend-tmp
	@mv .depend-tmp .depend

-include .depend
