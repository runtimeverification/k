# path to the current makefile
MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
# path to the kompile binary of this distribuition
KOMPILE=$(abspath $(MAKEFILE_PATH)/../bin/kompile)
# and kdep
KDEP=$(abspath $(MAKEFILE_PATH)/../bin/kdep)
# path to put -kompiled directory in
DEFDIR?=.
# default KOMPILE_BACKEND
KOMPILE_BACKEND?=ocaml

CHECK=| diff -

.PHONY: kompile all clean update-results

# run all tests
all: kompile

# run only kompile
kompile: $(DEFDIR)/$(DEF)-kompiled/timestamp

$(DEFDIR)/%-kompiled/timestamp: %.k
	$(KOMPILE) $(KOMPILE_FLAGS) --backend $(KOMPILE_BACKEND) $(DEBUG) $< -d $(DEFDIR) 2>&1 | sed 's!'`pwd`'/\(\./\)\?!!g' $(CHECK) $<.out $(CHECK2)

# run all tests and regenerate output files
update-results: kompile
update-results: CHECK=>
update-results: CHECK2=|| true

clean:
	rm -rf $(DEFDIR)/$(DEF)-kompiled

.depend:
	@$(KDEP) $(DEF).k > .depend-tmp
	@mv .depend-tmp .depend

-include .depend
