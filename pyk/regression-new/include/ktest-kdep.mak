MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
include $(MAKEFILE_PATH)/ktest-common.mak

# all tests in test directory with matching file extension
TESTS?=$(wildcard ./*.md) $(wildcard ./*.k)

CHECK=| diff -
PIPEFAIL?=set -o pipefail;

.PHONY: all

all: $(TESTS)

dummy:

%.k %.md: dummy
	$(PIPEFAIL) $(KDEP) $(KDEP_FLAGS) $@ $(REMOVE_PATHS) $(CHECK) $@.out

# run all tests and regenerate output files
update-results: all
update-results: CHECK=>

clean:
	rm -rf $(KOMPILED_DIR) .depend-tmp .depend .kompile-* .krun-* .kprove-* kore-exec.tar.gz
