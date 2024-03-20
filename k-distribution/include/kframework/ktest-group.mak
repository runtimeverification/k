SUBCLEAN=$(addsuffix .clean,$(SUBDIRS))
SUBUPDATE=$(addsuffix .update,$(SUBDIRS))
SUBKOMPILE=$(addsuffix .kompile,$(SUBDIRS))
SUBKRUN=$(addsuffix .krun,$(SUBDIRS))
SUBPROOFS=$(addsuffix .proofs,$(SUBDIRS))
SUBSEARCHES=$(addsuffix .searches,$(SUBDIRS))
SUBKAST=$(addsuffix .kast,$(SUBDIRS))

.PHONY: all update-results clean kompile krun proofs searches kast $(SUBDIRS) $(SUBCLEAN) $(SUBUPDATE) $(SUBKOMPILE) $(SUBKRUN) $(SUBPROOFS) $(SUBSEARCHES) $(SUBKAST)

all: $(SUBDIRS)
clean: $(SUBCLEAN)
update-results: $(SUBUPDATE)
kompile: $(SUBKOMPILE)
krun: $(SUBKRUN)
proofs: $(SUBPROOFS)
searches: $(SUBSEARCHES)
kast: $(SUBKAST)

$(SUBDIRS):
	$(MAKE) -C $@

$(SUBCLEAN): %.clean:
	$(MAKE) -C $* clean

$(SUBUPDATE): %.update:
	$(MAKE) -C $* update-results

$(SUBKOMPILE): %.kompile:
	$(MAKE) -C $* kompile

$(SUBKRUN): %.krun:
	$(MAKE) -C $* krun

$(SUBPROOFS): %.proofs:
	$(MAKE) -C $* proofs

$(SUBSEARCHES): %.searches:
	$(MAKE) -C $* searches

$(SUBKAST): %.kast:
	$(MAKE) -C $* kast
