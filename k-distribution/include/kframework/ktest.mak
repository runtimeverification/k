SHELL=/bin/bash

UNAME := $(shell uname)

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
# and kast
KAST=${K_BIN}/kast
# and kparse
KPARSE=${K_BIN}/kparse
# and kserver
KSERVER=${K_BIN}/kserver
# and ksearch
KSEARCH:=$(KRUN) --search-all
# and kprint
KPRINT=${K_BIN}/kprint
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

ifeq ($(UNAME), Darwin)
	KOMPILE_FLAGS+=--no-haskell-binary
endif

KOMPILE_FLAGS+=--no-exc-wrap
KPROVE_FLAGS+=--no-exc-wrap
KRUN_FLAGS+=--no-exc-wrap

KRUN_OR_LEGACY=$(KRUN)

CHECK?=| diff -
REMOVE_PATHS=| sed 's!'`pwd`'/\(\./\)\{0,2\}!!g'
CONSIDER_ERRORS=2>&1

PIPEFAIL?=set -o pipefail;
# null by default, add CONSIDER_PROVER_ERRORS=2>&1 to the local Makefile to test kprove output
#CONSIDER_PROVER_ERRORS=

.PHONY: kompile krun all clean update-results proofs

# run all tests
all: kompile krun proofs searches strat kast kast-bison kparse

# run only kompile
kompile: $(KOMPILED_DIR)/timestamp

$(KOMPILED_DIR)/timestamp: $(DEF).$(SOURCE_EXT)
	$(KOMPILE) $(KOMPILE_FLAGS) --backend $(KOMPILE_BACKEND) $(DEBUG) $< --output-definition $(KOMPILED_DIR)

krun: $(TESTS)

proofs: $(PROOF_TESTS)

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
	$(PIPEFAIL) (cat $@.in 2>/dev/null || true) | $(KRUN_OR_LEGACY) $@ $(KRUN_FLAGS) $(DEBUG) --definition $(KOMPILED_DIR) $(CHECK) $@.out
else
	$(PIPEFAIL) (cat $(RESULTDIR)/$(notdir $@).in 2>/dev/null || true) | $(KRUN_OR_LEGACY) $@ $(KRUN_FLAGS) $(DEBUG) --definition $(KOMPILED_DIR) $(CHECK) $(RESULTDIR)/$(notdir $@).out
endif

krun.nopgm: kompile
ifeq ($(TESTDIR),$(RESULTDIR))
	$(PIPEFAIL) (cat $@.in 2>/dev/null || true) | $(KRUN_OR_LEGACY) $(KRUN_FLAGS) $(DEBUG) --definition $(KOMPILED_DIR) $(CHECK) $@.out
else
	$(PIPEFAIL) (cat $(RESULTDIR)/$(notdir $@).in 2>/dev/null || true) | $(KRUN_OR_LEGACY) $(KRUN_FLAGS) $(DEBUG) --definition $(KOMPILED_DIR) $(CHECK) $(RESULTDIR)/$(notdir $@).out
endif

%-spec.k %-spec.md: kompile
ifeq ($(TESTDIR),$(RESULTDIR))
	$(KPROVE) $@ $(KPROVE_FLAGS) $(DEBUG) --definition $(KOMPILED_DIR) $(CONSIDER_PROVER_ERRORS) $(REMOVE_PATHS) $(CHECK) $@.out
else
	$(KPROVE) $@ $(KPROVE_FLAGS) $(DEBUG) --definition $(KOMPILED_DIR) $(CONSIDER_PROVER_ERRORS) $(REMOVE_PATHS) $(CHECK) $(RESULTDIR)/$(notdir $@).out
endif

%-broken-spec.k %-broken-spec.md: kompile
ifeq ($(TESTDIR),$(RESULTDIR))
	$(KPROVE) $@ $(KPROVE_FLAGS) $(DEBUG) --definition $(KOMPILED_DIR) $(CONSIDER_ERRORS) $(REMOVE_PATHS) $(CHECK) $@.out
else
	$(KPROVE) $@ $(KPROVE_FLAGS) $(DEBUG) --definition $(KOMPILED_DIR) $(CONSIDER_ERRORS) $(REMOVE_PATHS) $(CHECK) $(RESULTDIR)/$(notdir $@).out
endif

%.search: kompile
ifeq ($(TESTDIR),$(RESULTDIR))
	$(PIPEFAIL) $(KSEARCH) $@ $(KSEARCH_FLAGS) $(DEBUG) --definition $(KOMPILED_DIR) $(CHECK) $@.out
else
	$(PIPEFAIL) $(KSEARCH) $@ $(KSEARCH_FLAGS) $(DEBUG) --definition $(KOMPILED_DIR) $(CHECK) $(RESULTDIR)/$(notdir $@).out
endif

%.strat: kompile
ifeq ($(TESTDIR),$(RESULTDIR))
	$(PIPEFAIL) $(KRUN_OR_LEGACY) $@.input $(KRUN_FLAGS) $(DEBUG) --definition $(KOMPILED_DIR) -cSTRATEGY="$(shell cat $@)" $(CHECK) $@.out
else
	$(PIPEFAIL) $(KRUN_OR_LEGACY) $@.input $(KRUN_FLAGS) $(DEBUG) --definition $(KOMPILED_DIR) -cSTRATEGY="$(shell cat $@)" $(CHECK) $(RESULT_DIR)/$(notdir $@).out
endif

%.kast: kompile
ifeq ($(TESTDIR),$(RESULTDIR))
	$(PIPEFAIL) $(KAST) $@ $(KAST_FLAGS) $(DEBUG) --definition $(KOMPILED_DIR) $(CHECK) $@.out
else
	$(PIPEFAIL) $(KAST) $@ $(KAST_FLAGS) $(DEBUG) --definition $(KOMPILED_DIR) $(CHECK) $(RESULTDIR)/$(notdir $@).out
endif

%.kparse: kompile
ifeq ($(TESTDIR),$(RESULTDIR))
	$(PIPEFAIL) $(KPARSE) $@ $(KPARSE_FLAGS) $(DEBUG) --definition $(KOMPILED_DIR) $(CHECK) $@.out
else
	$(PIPEFAIL) $(KPARSE) $@ $(KPARSE_FLAGS) $(DEBUG) --definition $(KOMPILED_DIR) $(CHECK) $(RESULTDIR)/$(notdir $@).out
endif

%.kast-bison: kompile
	$(KAST) $(KAST_FLAGS) $(DEBUG) --definition $(KOMPILED_DIR) bison_parser
ifeq ($(TESTDIR),$(RESULTDIR))
	$(PIPEFAIL) ./bison_parser $@ $(CHECK) $@.out
else
	$(PIPEFAIL) ./bison_parser $@ $(CHECK) $(RESULTDIR)/$(notdir $@).out
endif

clean:
	rm -rf $(KOMPILED_DIR) .depend-tmp .depend .kompile-* .krun-* .kprove-* kore-exec.tar.gz

.depend:
	@$(KDEP) $(KDEP_FLAGS) $(DEF).$(SOURCE_EXT) > .depend-tmp
	@mv .depend-tmp .depend

ifneq ($(MAKECMDGOALS),clean)
-include .depend
endif
