# KCOMPILE can be set by whoever calls this file
# e.g., `make KCOMPILE=xxxxx`
KCOMPILE ?= $(shell which kompile)

# this is the name of the main maude module 
LANGUAGE_NAME = RUN

# this are all interesting modules (used to latexify)
LANGUAGE_MODULES = QUOTE-UNQUOTE

#this is the basename of the main file
MAIN_FILE = run

# this is a space-separated list of basename maude files to run
TESTS = test.m

TOOL_DIR = $(dir $(KCOMPILE))../tools/
include $(TOOL_DIR)make-helper.mk
