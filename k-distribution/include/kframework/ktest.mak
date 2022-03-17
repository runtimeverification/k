SHELL=/bin/bash

# path to the current makefile
MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
# path to binary directory of this distribution
K_BIN=$(abspath $(MAKEFILE_PATH)/../../bin)
# path to the kompile binary of this distribuition
KOMPILE=${K_BIN}/kompile
# ditto for krun
KRUN=${K_BIN}/krun
# and kdep
KDEP=${K_BIN}/kdep
# and kprove
KPROVE=${K_BIN}/kprove
KPROVEX=${K_BIN}/kprovex
# and kbmc
KBMC=${K_BIN}/kbmc
# and kast
KAST=${K_BIN}/kast
# and kparse
KPARSE=${K_BIN}/kparse
# and keq
KEQ=${K_BIN}/keq
# and kserver
KSERVER=${K_BIN}/kserver
# and ksearch
KSEARCH:=$(KRUN) --search-all
# and kprint
KPRINT=${K_BIN}/kprint
# and krun-legacy
KRUN_LEGACY=${K_BIN}/krun-legacy
# and llvm-krun
LLVM_KRUN=${K_BIN}/llvm-krun
# path relative to current definition of test programs
TESTDIR?=tests
# path to put -kompiled directory in
DEFDIR?=.
# path to kompile output directory
KOMPILED_DIR=$(DEFDIR)/$(notdir $(DEF))-kompiled
# path relative to current definition of output/input files
RESULTDIR?=$(TESTDIR)
# all tests in test directory with matching file extension
TESTS?=$(wildcard $(TESTDIR)/krun.nopgm) $(wildcard $(TESTDIR)/*.$(EXT))
PROOF_TESTS?=$(wildcard $(TESTDIR)/*-spec.k) $(wildcard $(TESTDIR)/*-spec.md)
BMC_TESTS?=$(wildcard $(TESTDIR)/*-spec-bmc.k) $(wildcard $(TESTDIR)/*-spec-bmc.md)
SEARCH_TESTS?=$(wildcard $(TESTDIR)/*.$(EXT).search)
STRAT_TESTS?=$(wildcard $(TESTDIR)/*.strat)
KAST_TESTS?=$(wildcard $(TESTDIR)/*.kast)
KPARSE_TESTS?=$(wildcard $(TESTDIR)/*.kparse)
KAST_BISON_TESTS?=$(wildcard $(TESTDIR)/*.kast-bison)
# default KOMPILE_BACKEND
KOMPILE_BACKEND?=llvm
# check if .k file exists, if not, check if .md file exists
# if not, default to .k to give error message
SOURCE_EXT?=$(or $(and $(wildcard $(DEF).k), k), $(or $(and $(wildcard $(DEF).md), md), k))
KOMPILE_FLAGS+=--no-exc-wrap
KPROVE_FLAGS+=--no-exc-wrap
KRUN_FLAGS+=--no-exc-wrap

KRUN_OR_LEGACY=$(KRUN)
KPROVE_OR_X=$(KPROVE)

CHECK?=| diff -
REMOVE_PATHS=| sed 's!'`pwd`'/\(\./\)\{0,2\}!!g'
CONSIDER_ERRORS=2>&1

PIPEFAIL?=set -o pipefail;
# null by default, add CONSIDER_PROVER_ERRORS=2>&1 to the local Makefile to test kprove output
#CONSIDER_PROVER_ERRORS=

.PHONY: kompile krun all clean update-results proofs bmc

# run all tests
all: kompile krun proofs bmc searches strat kast kast-bison kparse

# run only kompile
kompile: $(KOMPILED_DIR)/timestamp

$(KOMPILED_DIR)/timestamp: $(DEF).$(SOURCE_EXT)
	$(KOMPILE) $(KOMPILE_FLAGS) --backend $(KOMPILE_BACKEND) $(DEBUG) $< -d $(DEFDIR)

krun: $(TESTS)

proofs: $(PROOF_TESTS)

bmc: $(BMC_TESTS)

searches: $(SEARCH_TESTS)

strat: $(STRAT_TESTS)

kast: $(KAST_TESTS)

kparse: $(KPARSE_TESTS)

kast-bison: $(KAST_BISON_TESTS)

# run all tests and regenerate output files
update-results: all
update-results: CHECK=>

# run a single test. older versions of make run pattern rules in order, so
# if some programs should be run with different options their rule should be
# specified in the makefile prior to including ktest.mak.
%.$(EXT): kompile
ifeq ($(TESTDIR),$(RESULTDIR))
	$(PIPEFAIL) (cat $@.in 2>/dev/null || true) | $(KRUN_OR_LEGACY) $@ $(KRUN_FLAGS) $(DEBUG) -d $(DEFDIR) $(CHECK) $@.out
else
	$(PIPEFAIL) (cat $(RESULTDIR)/$(notdir $@).in 2>/dev/null || true) | $(KRUN_OR_LEGACY) $@ $(KRUN_FLAGS) $(DEBUG) -d $(DEFDIR) $(CHECK) $(RESULTDIR)/$(notdir $@).out
endif

krun.nopgm: kompile
ifeq ($(TESTDIR),$(RESULTDIR))
	$(PIPEFAIL) (cat $@.in 2>/dev/null || true) | $(KRUN_OR_LEGACY) $(KRUN_FLAGS) $(DEBUG) -d $(DEFDIR) $(CHECK) $@.out
else
	$(PIPEFAIL) (cat $(RESULTDIR)/$(notdir $@).in 2>/dev/null || true) | $(KRUN_OR_LEGACY) $(KRUN_FLAGS) $(DEBUG) -d $(DEFDIR) $(CHECK) $(RESULTDIR)/$(notdir $@).out
endif

%-spec.k %-spec.md: kompile
ifeq ($(TESTDIR),$(RESULTDIR))
	$(KPROVE_OR_X) $@ $(KPROVE_FLAGS) $(DEBUG) -d $(DEFDIR) $(CONSIDER_PROVER_ERRORS) $(REMOVE_PATHS) $(CHECK) $@.out
else
	$(KPROVE_OR_X) $@ $(KPROVE_FLAGS) $(DEBUG) -d $(DEFDIR) $(CONSIDER_PROVER_ERRORS) $(REMOVE_PATHS) $(CHECK) $(RESULTDIR)/$(notdir $@).out
endif

%-broken-spec.k %-broken-spec.md: kompile
ifeq ($(TESTDIR),$(RESULTDIR))
	$(KPROVE_OR_X) $@ $(KPROVE_FLAGS) $(DEBUG) -d $(DEFDIR) $(CONSIDER_ERRORS) $(REMOVE_PATHS) $(CHECK) $@.out
else
	$(KPROVE_OR_X) $@ $(KPROVE_FLAGS) $(DEBUG) -d $(DEFDIR) $(CONSIDER_ERRORS) $(REMOVE_PATHS) $(CHECK) $(RESULTDIR)/$(notdir $@).out
endif

%-spec-bmc.k %-spec-bmc.md: kompile
ifeq ($(TESTDIR),$(RESULTDIR))
	$(KBMC) --raw-spec $@ $(KBMC_FLAGS) $(DEBUG) -d $(DEFDIR) --depth 20 $(CHECK) $@.out
else
	$(KBMC) --raw-spec $@ $(KBMC_FLAGS) $(DEBUG) -d $(DEFDIR) --depth 20 $(CHECK) $(RESULTDIR)/$(notdir $@).out
endif

%.search: kompile
ifeq ($(TESTDIR),$(RESULTDIR))
	$(PIPEFAIL) $(KSEARCH) $@ $(KSEARCH_FLAGS) $(DEBUG) -d $(DEFDIR) $(CHECK) $@.out
else
	$(PIPEFAIL) $(KSEARCH) $@ $(KSEARCH_FLAGS) $(DEBUG) -d $(DEFDIR) $(CHECK) $(RESULTDIR)/$(notdir $@).out
endif

%.strat: kompile
ifeq ($(TESTDIR),$(RESULTDIR))
	$(PIPEFAIL) $(KRUN_OR_LEGACY) $@.input $(KRUN_FLAGS) $(DEBUG) -d $(DEFDIR) -cSTRATEGY="$(shell cat $@)" $(CHECK) $@.out
else
	$(PIPEFAIL) $(KRUN_OR_LEGACY) $@.input $(KRUN_FLAGS) $(DEBUG) -d $(DEFDIR) -cSTRATEGY="$(shell cat $@)" $(CHECK) $(RESULT_DIR)/$(notdir $@).out
endif

%.kast: kompile
ifeq ($(TESTDIR),$(RESULTDIR))
	$(PIPEFAIL) $(KAST) $@ $(KAST_FLAGS) $(DEBUG) -d $(DEFDIR) $(CHECK) $@.out
else
	$(PIPEFAIL) $(KAST) $@ $(KAST_FLAGS) $(DEBUG) -d $(DEFDIR) $(CHECK) $(RESULTDIR)/$(notdir $@).out
endif

%.kparse: kompile
ifeq ($(TESTDIR),$(RESULTDIR))
	$(PIPEFAIL) $(KPARSE) $@ $(KPARSE_FLAGS) $(DEBUG) -d $(DEFDIR) $(CHECK) $@.out
else
	$(PIPEFAIL) $(KPARSE) $@ $(KPARSE_FLAGS) $(DEBUG) -d $(DEFDIR) $(CHECK) $(RESULTDIR)/$(notdir $@).out
endif

%.kast-bison: kompile
	$(KAST) $(KAST_FLAGS) $(DEBUG) -d $(DEFDIR) bison_parser
ifeq ($(TESTDIR),$(RESULTDIR))
	$(PIPEFAIL) ./bison_parser $@ $(CHECK) $@.out
else
	$(PIPEFAIL) ./bison_parser $@ $(CHECK) $(RESULTDIR)/$(notdir $@).out
endif

clean:
	rm -rf $(KOMPILED_DIR) .depend-tmp .depend .kompile-* .krun-* .kprove-* .kbmc-* kore-exec.tar.gz

.depend:
	@$(KDEP) $(KDEP_FLAGS) $(DEF).$(SOURCE_EXT) > .depend-tmp
	@mv .depend-tmp .depend

ifneq ($(MAKECMDGOALS),clean)
-include .depend
endif
