# path to the current makefile
MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
# path to the kompile binary of this distribuition
KOMPILE=$(abspath $(MAKEFILE_PATH)/../bin/kompile)
# and kdep
KDEP=$(abspath $(MAKEFILE_PATH)/../bin/kdep)
# path to put -kompiled directory in
DEFDIR?=.
# all tests in test directory with matching file extension
TESTS?=$(wildcard $(DEFDIR)/*.k)
# default KOMPILE_BACKEND
KOMPILE_BACKEND?=ocaml

CHECK=| diff -

.PHONY: kompile all clean update-results dummy

# run all tests
all: kompile

# run only kompile
kompile: $(TESTS)

dummy:

%.k: dummy
	$(KOMPILE) $(KOMPILE_FLAGS) --backend $(KOMPILE_BACKEND) $(DEBUG) $@ -d $(DEFDIR) 2>&1 | sed 's!'`pwd`'/\(\./\)\{0,1\}!!g' $(CHECK) $@.out $(CHECK2)

# run all tests and regenerate output files
update-results: kompile
update-results: CHECK=>
update-results: CHECK2=|| true

clean:
	rm -rf $(DEFDIR)/*-kompiled
