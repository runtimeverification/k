#####################################################################
# KCOMPILE can be set by whoever calls this file
# e.g., `make KCOMPILE=xxxxx`
#KCOMPILE ?= $(shell which kompile)
#TOOL_DIR = $(K_CORE)/../tools/
#include $(TOOL_DIR)make-helper.mk
#####################################################################

space = $(empty) $(empty)
# $(call space-to-bang,file-name)
space-to-bang = $(subst $(space),!,$1)
# $(call bang-to-space,file-name)
bang-to-space = $(subst !,\$(space),$1)

# get a list of all the subdirectories
#DIRS = ${subst /,, ${subst ./,, ${filter-out ./,${sort ${dir ${wildcard ./*/}}}}}}
DIRS = $(subst /,, $(subst ./,, $(filter-out ./,$(sort $(dir $(subst !./, ./,$(call space-to-bang, ${wildcard ./*/})))))))

.PHONY: all clean $(DIRS)

all: $(DIRS)
	@echo Checked: $(call bang-to-space, $(DIRS))

$(DIRS):
	@echo Testing $(call bang-to-space, $@)...
	@(ulimit -t 25 && make -C $(call bang-to-space, $@) true-test)
	@echo Done with $(call bang-to-space, $@).
		
clean: 
	$(foreach dir,$(DIRS),if ! make -C $(call bang-to-space, $(dir)) clean ; then echo FAILURE!; exit 1; fi;)
#@for d in $(DIRS); do echo $(call bang-to-space, $$d); if ! make -C $(call bang-to-space, $$d) clean ; then echo FAILURE!; exit 1; fi; done
