# KCOMPILE can be set by whoever calls this file
# e.g., `make KCOMPILE=xxxxx`
KCOMPILE ?= $(shell which kompile)

# this is the name of the main maude module 
LANGUAGE_NAME = GRAPH-COLORING

# this is the name of the interesting modules (used by make latex/pdf) 
LANGUAGE_MODULES = GRAPH-COLORING-SEMANTICS

#this is the basename of the main file
MAIN_FILE = graph-coloring

# this is a space-separated list of basename maude files to run
TESTS = test.m

TOOL_DIR = $(dir $(KCOMPILE))
include $(TOOL_DIR)make-helper.mk
