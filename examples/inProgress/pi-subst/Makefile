# KCOMPILE can be set by whoever calls this file
# e.g., `make KCOMPILE=xxxxx`
KCOMPILE ?= $(shell which kompile)

# this is the name of the main maude module 
LANGUAGE_NAME = PI

# this are all interesting modules (used to latexify)
LANGUAGE_MODULES = PI-SYNTAX PI-SEMANTICS 

#this is the basename of the main file
MAIN_FILE = pi

# this is a space-separated list of basename maude files to run
TESTS = pi-test.m

TOOL_DIR = $(dir $(KCOMPILE))
include $(TOOL_DIR)make-helper.mk
