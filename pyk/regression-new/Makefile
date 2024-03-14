SKIPPED=$(shell cat skipped)
SUBDIRS=$(filter-out Makefile include $(SKIPPED), $(wildcard *))
include ./include/ktest-group.mak
