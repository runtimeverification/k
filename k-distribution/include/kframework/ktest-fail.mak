MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
include $(MAKEFILE_PATH)/ktest-common.mak

# path to put -kompiled directory in
DEFDIR?=.
# all tests in test directory with matching file extension
TESTS?=$(wildcard $(DEFDIR)/*.md) $(wildcard $(DEFDIR)/*.k)
# default KOMPILE_BACKEND
KOMPILE_BACKEND?=llvm
KAST_TESTS?=$(wildcard ./*.kast)

KOMPILE_FLAGS+=--no-exc-wrap --type-inference-mode checked
KPROVE_FLAGS+=--no-exc-wrap
KRUN_FLAGS+=--no-exc-wrap

CHECK=| diff -

.PHONY: kompile all clean update-results dummy krun proofs searches kast

# run all tests
all: kompile kast

# run only kompile
kompile: $(TESTS)

kast: $(KAST_TESTS)

dummy:

%.k %.md: dummy
	$(KOMPILE) $(KOMPILE_FLAGS) --backend $(KOMPILE_BACKEND) $(DEBUG_FAIL) $@ --output-definition $(DEFDIR)/$(basename $@)-kompiled 2>&1 $(REMOVE_PATHS) $(CHECK) $@.out $(CHECK2)

%.kast: kompile
	$(KAST) $@ $(KAST_FLAGS) $(DEBUG) 2>&1 $(REMOVE_PATHS) $(CHECK) $@.out

# run all tests and regenerate output files
update-results: kompile kast
update-results: CHECK=>
update-results: CHECK2=|| true

clean:
	rm -rf $(DEFDIR)/*-kompiled
