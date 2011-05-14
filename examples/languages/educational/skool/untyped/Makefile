# KCOMPILE can be set by whoever calls this file
# e.g., `make KCOMPILE=xxxxx`
KCOMPILE ?= $(shell which kompile)

# this is the name of the main maude module 
LANGUAGE_NAME = SKOOL-UNTYPED

# this are all interesting modules (used to latexify)
LANGUAGE_MODULES = SKOOL-UNTYPED-SYNTAX SKOOL-UNTYPED-SEMANTICS SKOOL-UNTYPED

LATEX_STYLE = bb

#this is the basename of the main file
MAIN_FILE = skool-untyped

# this is a space-separated list of basename maude files to run
TESTS = skool-untyped-test.m

TOOL_DIR = $(dir $(KCOMPILE))../tools/
include $(TOOL_DIR)make-helper.mk

