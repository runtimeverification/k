SKIPPED=$(shell cat skipped)
SUBDIRS=$(filter-out Makefile include skipped $(SKIPPED), $(wildcard *))
include ./include/ktest-group.mak
