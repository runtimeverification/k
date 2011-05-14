# KCOMPILE can be set by whoever calls this file
# e.g., `make KCOMPILE=xxxxx`
KCOMPILE ?= $(shell which kompile)

# this is the name of the main maude module 
LANGUAGE_NAME = CHALLENGE

# these are the interesting modules in the language (used by make latex/pdf)
LANGUAGE_MODULES = CHALLENGE-SYNTAX CHALLENGE-DESUGARED-SYNTAX CHALLENGE-SEMANTICS CHALLENGE

#this is the basename of the main file
MAIN_FILE = challenge

# this is a space-separated list of basename maude files to run
TESTS = challenge-test.m

TOOL_DIR = $(dir $(KCOMPILE))
include $(TOOL_DIR)make-helper.mk
