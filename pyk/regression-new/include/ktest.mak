SHELL=/bin/bash

UNAME := $(shell uname)

ROOT=$(abspath $(MAKEFILE_PATH)/../..)
POETRY_RUN?=poetry run -C $(ROOT)
# path to the current makefile
MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
# path to the kompile binary of this distribuition
KOMPILE=$(POETRY_RUN) pyk kompile
# ditto for krun
KRUN=$(POETRY_RUN) pyk run
# and kdep
KDEP=$(POETRY_RUN) pyk kdep
# and kprove
KPROVE=$(POETRY_RUN) pyk prove
# and kast
KAST=$(POETRY_RUN) pyk parse
# and kparse
KPARSE=$(POETRY_RUN) pyk parse
# and kserver
KSERVER=$(POETRY_RUN) pyk kserver
# and ksearch
KSEARCH:=$(KRUN) --search-all
# and kprint
KPRINT=$(POETRY_RUN) pyk parse
# and llvm-krun
LLVM_KRUN=$(POETRY_RUN) pyk llvm-krun
# path relative to current definition of test programs
TESTDIR?=tests
# path relative to current definition of output/input files
RESULTDIR?=$(TESTDIR)
# path to put -kompiled directory in
DEFDIR?=.
# path to kompile output directory
KOMPILED_DIR=$(DEFDIR)/$(notdir $(DEF))-kompiled
# all tests in test directory with matching file extension
RUN_TESTS?=$(wildcard $(TESTDIR)/*.$(EXT))
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

VERBOSITY?=

ifeq ($(UNAME), Darwin)
	KOMPILE_FLAGS+=--no-haskell-binary
endif

KOMPILE_FLAGS+=--type-inference-mode checked $(VERBOSITY)
KRUN_FLAGS+=
KPROVE_FLAGS+=--type-inference-mode checked --failure-info $(VERBOSITY)

CHECK?=| diff -
REMOVE_PATHS=| sed 's!'`pwd`'/\(\./\)\{0,2\}!!g'
CONSIDER_ERRORS=2>&1

PIPEFAIL?=set -o pipefail;
# null by default, add CONSIDER_PROVER_ERRORS=2>&1 to the local Makefile to test kprove output
#CONSIDER_PROVER_ERRORS=

.PHONY: kompile all clean update-results proofs krun searches strat kast kast-bison kparse

# run all tests
all: kompile krun proofs searches strat kast kast-bison kparse

# run only kompile
kompile: $(KOMPILED_DIR)/timestamp

$(KOMPILED_DIR)/timestamp: $(DEF).$(SOURCE_EXT)
	$(KOMPILE) $(KOMPILE_FLAGS) --backend $(KOMPILE_BACKEND) $(DEBUG) $< --output-definition $(KOMPILED_DIR)

krun: $(RUN_TESTS)

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
	$(PIPEFAIL) (cat $@.in 2>/dev/null || true) | $(KRUN) $@ $(KRUN_FLAGS) $(DEBUG) --definition $(KOMPILED_DIR) $(CHECK) $@.out
else
	$(PIPEFAIL) (cat $(RESULTDIR)/$(notdir $@).in 2>/dev/null || true) | $(KRUN) $@ $(KRUN_FLAGS) $(DEBUG) --definition $(KOMPILED_DIR) $(CHECK) $(RESULTDIR)/$(notdir $@).out
endif

krun.nopgm: kompile
ifeq ($(TESTDIR),$(RESULTDIR))
	$(PIPEFAIL) (cat $@.in 2>/dev/null || true) | $(KRUN) $(KRUN_FLAGS) $(DEBUG) --definition $(KOMPILED_DIR) $(CHECK) $@.out
else
	$(PIPEFAIL) (cat $(RESULTDIR)/$(notdir $@).in 2>/dev/null || true) | $(KRUN) $(KRUN_FLAGS) $(DEBUG) --definition $(KOMPILED_DIR) $(CHECK) $(RESULTDIR)/$(notdir $@).out
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
	$(PIPEFAIL) $(KRUN) $@.input $(KRUN_FLAGS) $(DEBUG) --definition $(KOMPILED_DIR) -cSTRATEGY="$(shell cat $@)" $(CHECK) $@.out
else
	$(PIPEFAIL) $(KRUN) $@.input $(KRUN_FLAGS) $(DEBUG) --definition $(KOMPILED_DIR) -cSTRATEGY="$(shell cat $@)" $(CHECK) $(RESULT_DIR)/$(notdir $@).out
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
	rm -rf $(KOMPILED_DIR) .kompile-* .krun-* .kprove-* kore-exec.tar.gz
ifeq ($(KOMPILE_BACKEND),kore)
	rm -f $(DEF).kore
endif
