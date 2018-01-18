MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
KOMPILE=$(abspath $(MAKEFILE_PATH)/../bin/kompile)
KRUN=$(abspath $(MAKEFILE_PATH)/../bin/krun)
KDEP=$(abspath $(MAKEFILE_PATH)/../bin/kdep)
TESTDIR?=tests
DEFDIR?=.
RESULTDIR?=$(TESTDIR)
TESTS=$(wildcard $(TESTDIR)/*.$(EXT))

CHECK=| diff -

.PHONY: kompile krun all clean update-results

all: kompile krun

kompile: $(DEFDIR)/$(DEF)-kompiled/timestamp

$(DEFDIR)/%-kompiled/timestamp: %.k
	$(KOMPILE) $(KOMPILE_FLAGS) $< -d $(DEFDIR)

krun: $(TESTS)

update-results: krun
update-results: CHECK=>

%.$(EXT): kompile
ifeq ($(TESTDIR),$(RESULTDIR))
	cat $@.in 2>/dev/null | $(KRUN) $@ $(KRUN_FLAGS) -d $(DEFDIR) $(CHECK) $@.out
else
	cat $(RESULTDIR)/$(notdir $@).in 2>/dev/null | $(KRUN) $@ $(KRUN_FLAGS) -d $(DEFDIR) $(CHECK) $(RESULTDIR)/$(notdir $@).out
endif

clean:
	rm -rf $(DEFDIR)/$(DEF)-kompiled

.depend:
	@$(KDEP) $(DEF).k > .depend-tmp
	@mv .depend-tmp .depend

-include .depend
