# path to the current makefile
MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
# path to the kdep binary of this distribuition
KDEP=$(abspath $(MAKEFILE_PATH)/../../bin/kdep)
# all tests in test directory with matching file extension
TESTS?=$(wildcard ./*.md) $(wildcard ./*.k)

CHECK=| diff -

.PHONY: all

all: $(TESTS)

dummy:

%.k %.md: dummy
	$(KDEP) $(OPTS) $@ $(CHECK) $@.out
