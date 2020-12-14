# path to the current makefile
MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
# path to the kompile binary of this distribuition
KOMPILE=$(abspath $(MAKEFILE_PATH)/../../bin/kompile)
# ditto for krun
KRUN=$(abspath $(MAKEFILE_PATH)/../../bin/krun)
# and kdep
KDEP=$(abspath $(MAKEFILE_PATH)/../../bin/kdep)
# path to put -kompiled directory in
DEFDIR?=.
# all tests in test directory with matching file extension
TESTS?=$(wildcard $(DEFDIR)/*.md) $(wildcard $(DEFDIR)/*.k)
# all tests to run
TESTS_KRUN?=$(wildcard $(TESTDIR)/*.$(EXT))
# default KOMPILE_BACKEND
KOMPILE_BACKEND?=llvm
ifeq ($(KOMPILE_BACKEND),llvm)
KRUN=$(abspath $(MAKEFILE_PATH)/../../bin/kx)
endif
ifeq ($(KOMPILE_BACKEND),haskell)
KRUN=$(abspath $(MAKEFILE_PATH)/../../bin/kx)
endif

CHECK=| diff -

.PHONY: kompile all clean update-results dummy krun proofs bmc searches strat kast

# run all tests
all: kompile krun

# run only kompile
kompile: $(TESTS)

krun: $(TESTS_KRUN)

dummy:

%.$(EXT): kompile
	cat $@.in 2>/dev/null | $(KRUN) $@ $(KRUN_FLAGS) $(DEBUG) -d $(DEFDIR) 2>&1 | sed 's!'`pwd`'/\(\./\)\{0,2\}!!g' $(CHECK) $@.out $(CHECK2)

%.k %.md: dummy
	$(KOMPILE) $(KOMPILE_FLAGS) --backend $(KOMPILE_BACKEND) $(DEBUG_FAIL) $@ -d $(DEFDIR) 2>&1 | sed 's!'`pwd`'/\(\./\)\{0,2\}!!g' $(CHECK) $@.out $(CHECK2)

# run all tests and regenerate output files
update-results: kompile krun
update-results: CHECK=>
update-results: CHECK2=|| true

clean:
	rm -rf $(DEFDIR)/*-kompiled .depend-tmp .depend
