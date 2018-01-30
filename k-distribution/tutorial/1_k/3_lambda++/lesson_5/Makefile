MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
SUBMAKES=$(MAKEFILE_PATH)/Makefile.det $(MAKEFILE_PATH)/Makefile.nondet
SUBCLEAN=$(addsuffix .clean,$(SUBMAKES))
SUBUPDATE=$(addsuffix .update,$(SUBMAKES))

.PHONY: all clean $(SUBMAKES) $(SUBCLEAN) $(SUBUPDATE)

all: $(SUBMAKES)
clean: $(SUBCLEAN)
update-results: $(SUBUPDATE)

$(SUBMAKES):
	$(MAKE) -e -f $@

$(SUBCLEAN): %.clean:
	$(MAKE) -e -f $* clean

$(SUBUPDATE): %.update:
	$(MAKE) -e -f $* update-results
