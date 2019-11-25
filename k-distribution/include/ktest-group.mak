SUBCLEAN=$(addsuffix .clean,$(SUBDIRS))
SUBUPDATE=$(addsuffix .update,$(SUBDIRS))
SUBKOMPILE=$(addsuffix .kompile,$(SUBDIRS))

.PHONY: all update-results clean $(SUBDIRS) $(SUBCLEAN) $(SUBUPDATE) $(SUBKOMPILE)

all: $(SUBDIRS)
clean: $(SUBCLEAN)
update-results: $(SUBUPDATE)
kompile: $(SUBKOMPILE)

$(SUBDIRS):
	$(MAKE) -C $@

$(SUBCLEAN): %.clean:
	$(MAKE) -C $* clean

$(SUBUPDATE): %.update:
	$(MAKE) -C $* update-results

$(SUBKOMPILE): %.kompile:
	$(MAKE) -C $* kompile
