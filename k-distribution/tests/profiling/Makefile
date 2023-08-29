EXCLUDE=Makefile kprofiling.mak setup_profiling.sh
SUBDIRS=$(filter-out $(EXCLUDE), $(wildcard *))

SUBCLEAN=$(addsuffix .clean,$(SUBDIRS))
SUBPROFILE=$(addsuffix .profile,$(SUBDIRS))

.PHONY: all clean profile $(SUBDIRS) $(SUBCLEAN) $(SUBPROFILE)

all: $(SUBDIRS)
clean: $(SUBCLEAN)
profile: $(SUBPROFILE)

$(SUBDIRS):
	$(MAKE) -C $@

$(SUBCLEAN): %.clean:
	$(MAKE) -C $* clean

$(SUBPROFILE): %.profile:
	$(MAKE) -C $* profile
