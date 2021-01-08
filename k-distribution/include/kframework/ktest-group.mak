SUBCLEAN=$(addsuffix .clean,$(SUBDIRS))
SUBUPDATE=$(addsuffix .update,$(SUBDIRS))
SUBKOMPILE=$(addsuffix .kompile,$(SUBDIRS))
SUBKRUN=$(addsuffix .krun,$(SUBDIRS))
SUBPROOFS=$(addsuffix .proofs,$(SUBDIRS))
SUBBMC=$(addsuffix .bmc,$(SUBDIRS))
SUBSEARCHES=$(addsuffix .searches,$(SUBDIRS))
SUBSTRAT=$(addsuffix .strat,$(SUBDIRS))
SUBKAST=$(addsuffix .kast,$(SUBDIRS))

.PHONY: all update-results clean kompile krun proofs bmc searches strat kast $(SUBDIRS) $(SUBCLEAN) $(SUBUPDATE) $(SUBKOMPILE) $(SUBKRUN) $(SUBPROOFS) $(SUBBMC) $(SUBSEARCHES) $(SUBSTRAT) $(SUBKAST)

all: $(SUBDIRS)
clean: $(SUBCLEAN)
update-results: $(SUBUPDATE)
kompile: $(SUBKOMPILE)
krun: $(SUBKRUN)
proofs: $(SUBPROOFS)
bmc: $(SUBBMC)
searches: $(SUBSEARCHES)
strat: $(SUBSTRAT)
kast: $(SUBKAST)

SHELL=/bin/bash -o pipefail

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

$(SUBBMC): %.bmc:
	$(MAKE) -C $* bmc

$(SUBSEARCHES): %.searches:
	$(MAKE) -C $* searches

$(SUBSTRAT): %.strat:
	$(MAKE) -C $* strat

$(SUBKAST): %.kast:
	$(MAKE) -C $* kast
