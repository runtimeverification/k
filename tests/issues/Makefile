#####################################################################
# KCOMPILE can be set by whoever calls this file
# e.g., `make KCOMPILE=xxxxx`
#KCOMPILE ?= $(shell which kompile)
#TOOL_DIR = $(dir $(KCOMPILE))
#include $(TOOL_DIR)make-helper.mk
#####################################################################

# get a list of all the subdirectories
DIRS = ${subst /,, ${subst ./,, ${filter-out ./,${sort ${dir ${wildcard ./*/}}}}}}

.PHONY: all clean $(DIRS)

all: $(DIRS)
	@echo Checked: $(DIRS)

$(DIRS):
	@echo Testing $@...
	@(ulimit -t 25 && make -C $@ true-test)
	@echo Done with $@.
		
clean: 
	@for d in $(DIRS); do if ! make -C $$d clean ; then echo FAILURE!; exit 1; fi; done
