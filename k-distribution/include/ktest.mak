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
# and kbmc
KBMC=$(abspath $(MAKEFILE_PATH)/../bin/kbmc)
# and kast
KAST=$(abspath $(MAKEFILE_PATH)/../bin/kast)
# and keq
KEQ=$(abspath $(MAKEFILE_PATH)/../bin/keq)
# and kserver
KSERVER=$(abspath $(MAKEFILE_PATH)/../bin/kserver)
# and ksearch
KSEARCH=$(abspath $(MAKEFILE_PATH)/../bin/krun) --search-all
# and kast
KAST=$(abspath $(MAKEFILE_PATH)/../bin/kast)
# path relative to current definition of test programs
TESTDIR?=tests
# path to put -kompiled directory in
DEFDIR?=.
# path relative to current definition of output/input files
RESULTDIR?=$(TESTDIR)
# all tests in test directory with matching file extension
TESTS?=$(wildcard $(TESTDIR)/*.$(EXT))
PROOF_TESTS?=$(wildcard $(TESTDIR)/*-spec.k)
BMC_TESTS?=$(wildcard $(TESTDIR)/*-spec-bmc.k)
SEARCH_TESTS?=$(wildcard $(TESTDIR)/*.$(EXT).search)
STRAT_TESTS?=$(wildcard $(TESTDIR)/*.strat)
KAST_TESTS?=$(wildcard $(TESTDIR)/*.kast)
# default KOMPILE_BACKEND
KOMPILE_BACKEND?=ocaml

CHECK=| diff -

.PHONY: kompile krun all clean update-results proofs bmc

# run all tests
all: kompile krun proofs bmc searches strat kast

# run only kompile
kompile: $(DEFDIR)/$(DEF)-kompiled/timestamp

$(DEFDIR)/%-kompiled/timestamp: %.k
	$(KOMPILE) $(KOMPILE_FLAGS) --backend $(KOMPILE_BACKEND) $(DEBUG) $< -d $(DEFDIR)

krun: $(TESTS)

proofs: $(PROOF_TESTS)

bmc: $(BMC_TESTS)

searches: $(SEARCH_TESTS)

strat: $(STRAT_TESTS)

kast: $(KAST_TESTS)

# run all tests and regenerate output files
update-results: all
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
ifeq ($(TESTDIR),$(RESULTDIR))
	$(KPROVE) $@ $(KPROVE_FLAGS) $(DEBUG) -d $(DEFDIR) $(CHECK) $@.out
else
	$(KPROVE) $@ $(KPROVE_FLAGS) $(DEBUG) -d $(DEFDIR) $(CHECK) $(RESULTDIR)/$(notdir $@).out
endif

%-spec-bmc.k: kompile
ifeq ($(TESTDIR),$(RESULTDIR))
	$(KBMC) --raw-spec $@ $(KBMC_FLAGS) $(DEBUG) -d $(DEFDIR) --depth 20 $(CHECK) $@.out
else
	$(KBMC) --raw-spec $@ $(KBMC_FLAGS) $(DEBUG) -d $(DEFDIR) --depth 20 $(CHECK) $(RESULTDIR)/$(notdir $@).out
endif

%.search: kompile
ifeq ($(TESTDIR),$(RESULTDIR))
	$(KSEARCH) $@ $(KSEARCH_FLAGS) $(DEBUG) -d $(DEFDIR) $(CHECK) $@.out
else
	$(KSEARCH) $@ $(KSEARCH_FLAGS) $(DEBUG) -d $(DEFDIR) $(CHECK) $(RESULTDIR)/$(notdir $@).out
endif

%.strat: kompile
ifeq ($(TESTDIR),$(RESULTDIR))
	$(KRUN) $@.input $(KRUN_FLAGS) $(DEBUG) -d $(DEFDIR) -cSTRATEGY="$(shell cat $@)" $(CHECK) $@.out
else
	$(KRUN) $@.input $(KRUN_FLAGS) $(DEBUG) -d $(DEFDIR) -cSTRATEGY="$(shell cat $@)" $(CHECK) $(RESULT_DIR)/$(notdir $@).out
endif

%.kast: kompile
ifeq ($(TESTDIR),$(RESULTDIR))
	$(KAST) $@ $(KAST_FLAGS) $(DEBUG) -d $(DEFDIR) $(CHECK) $@.out
else
	$(KAST) $@ $(KAST_FLAGS) $(DEBUG) -d $(DEFDIR) $(CHECK) $(RESULTDIR)/$(notdir $@).out
endif

clean:
	rm -rf $(DEFDIR)/$(DEF)-kompiled

.depend:
	@$(KDEP) $(DEF).k > .depend-tmp
	@mv .depend-tmp .depend

-include .depend
