MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
SUBMAKES=$(MAKEFILE_PATH)/Makefile.det $(MAKEFILE_PATH)/Makefile.nondet
SUBCLEAN=$(addsuffix .clean,$(SUBMAKES))
SUBUPDATE=$(addsuffix .update,$(SUBMAKES))
SUBKOMPILE=$(addsuffix .kompile,$(SUBMAKES))

.PHONY: all update-results clean $(SUBMAKES) $(SUBCLEAN) $(SUBUPDATE) $(SUBKOMPILE)

all: $(SUBMAKES)
clean: $(SUBCLEAN)
update-results: $(SUBUPDATE)
kompile: $(SUBKOMPILE)

$(SUBMAKES):
	$(MAKE) -e -f $@

$(SUBCLEAN): %.clean:
	$(MAKE) -e -f $* clean

$(SUBUPDATE): %.update:
	$(MAKE) -e -f $* update-results

$(SUBKOMPILE): %.kompile:
	$(MAKE) -e -f $* kompile
