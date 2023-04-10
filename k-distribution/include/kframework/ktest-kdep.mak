SHELL=/bin/bash

# path to the current makefile
MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
# path to the kdep binary of this distribuition
K_BIN=$(abspath $(MAKEFILE_PATH)/../../bin)
KDEP=${K_BIN}/kdep
# all tests in test directory with matching file extension
TESTS?=$(wildcard ./*.md) $(wildcard ./*.k)

CHECK=| diff -
PIPEFAIL?=set -o pipefail;

.PHONY: all

all: $(TESTS)

dummy:

%.k %.md: dummy
	$(PIPEFAIL) $(KDEP) $(KDEP_FLAGS) $@ | sed 's!'`pwd`'/\(\./\)\{0,2\}!!g' $(CHECK) $@.out

# run all tests and regenerate output files
update-results: all
update-results: CHECK=>

clean:
	rm -rf $(KOMPILED_DIR) .depend-tmp .depend .kompile-* .krun-* .kprove-* kore-exec.tar.gz
