SUBCLEAN=$(addsuffix .clean,$(SUBDIRS))
SUBUPDATE=$(addsuffix .update,$(SUBDIRS))
SUBKOMPILE=$(addsuffix .kompile,$(SUBDIRS))
SUBPROOFS=$(addsuffix .proofs,$(SUBDIRS))

.PHONY: all update-results clean kompile proofs $(SUBDIRS) $(SUBCLEAN) $(SUBUPDATE) $(SUBKOMPILE) $(SUBPROOFS)

all: $(SUBDIRS)
clean: $(SUBCLEAN)
update-results: $(SUBUPDATE)
kompile: $(SUBKOMPILE)
proofs: $(SUBPROOFS)

$(SUBDIRS):
	$(MAKE) -C $@

$(SUBCLEAN): %.clean:
	$(MAKE) -C $* clean

$(SUBUPDATE): %.update:
	$(MAKE) -C $* update-results

$(SUBKOMPILE): %.kompile:
	$(MAKE) -C $* kompile

$(SUBPROOFS): %.proofs:
	$(MAKE) -C $* proofs
