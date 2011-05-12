# KCOMPILE can be set by whoever calls this file
# e.g., `make KCOMPILE=xxxxx`
KCOMPILE ?= $(shell which kompile)

# this is the name of the main maude module 
LANGUAGE_NAME = IMP

# this is the name of the interesting modules (used by make latex/pdf) 
LANGUAGE_MODULES = IMP-SYNTAX IMP-SEMANTICS IMP

#this is the basename of the main file
MAIN_FILE = imp

# this is a space-separated list of basename maude files to run
TESTS = imp-test.m

TOOL_DIR = $(dir $(KCOMPILE))
include $(TOOL_DIR)make-helper.mk
