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
# and kprove_ini
KPROVE_INI=$(abspath $(MAKEFILE_PATH)/../bin/kprove_ini)
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
ifeq ($(wildcard spec.ini),)
PROOF_TESTS?=$(wildcard $(TESTDIR)/*-spec.k)
else
PROOF_TESTS:=$(shell $(KPROVE_INI) $(TESTDIR)/defn-tmpl.k $(TESTDIR)/rule-tmpl.k $(TESTDIR)/spec.ini)
PROOF_INI_GENERATED:=true
endif
SEARCH_TESTS?=$(wildcard $(TESTDIR)/*.$(EXT).search)
STRAT_TESTS?=$(wildcard $(TESTDIR)/*.strat)
KAST_TESTS?=$(wildcard $(TESTDIR)/*.kast)
# default KOMPILE_BACKEND
KOMPILE_BACKEND?=ocaml

CHECK=| diff -

.PHONY: kompile krun all clean update-results proofs

# run all tests
all: kompile krun proofs searches strat kast

# run only kompile
kompile: $(DEFDIR)/$(DEF)-kompiled/timestamp

$(DEFDIR)/%-kompiled/timestamp: %.k
	$(KOMPILE) $(KOMPILE_FLAGS) --backend $(KOMPILE_BACKEND) $(DEBUG) $< -d $(DEFDIR)

krun: $(TESTS)

proofs: $(PROOF_TESTS)

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
ifeq ($(PROOF_INI_GENERATED),true)
ifeq ($(TESTDIR),$(RESULTDIR))
	cat $@ $(CHECK) $@.ini-out
else
	cat $@ $(CHECK) $(RESULTDIR)/$(notdir @).ini-out
endif
endif
ifeq ($(TESTDIR),$(RESULTDIR))
	$(KPROVE) $@ $(KPROVE_FLAGS) $(DEBUG) -d $(DEFDIR) $(CHECK) $@.out
else
	$(KPROVE) $@ $(KPROVE_FLAGS) $(DEBUG) -d $(DEFDIR) $(CHECK) $(RESULTDIR)/$(notdir $@).out
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
ifeq ($(PROOF_INI_GENERATED),true)
	rm -rf $(PROOF_TESTS)
endif

.depend:
	@$(KDEP) $(DEF).k > .depend-tmp
	@mv .depend-tmp .depend

-include .depend
