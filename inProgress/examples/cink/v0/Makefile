# KCOMPILE can be set by whoever calls this file
# e.g., `make KCOMPILE=xxxxx`
KCOMPILE ?= $(shell which kompile)

# this is the name of the main maude module 
LANGUAGE_NAME = CINK

# this are all interesting modules (used to latexify)
LANGUAGE_MODULES = CINK-SYNTAX CINK-DESUGARED-SYNTAX CINK-SEMANTICS CINK


LATEX_STYLE = bb

#this is the basename of the main file
MAIN_FILE = cink

# this is a space-separated list of basename maude files to run
TESTS = cink-test.m

TOOL_DIR = $(dir $(KCOMPILE))
include $(TOOL_DIR)make-helper.mk
