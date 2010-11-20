# KCOMPILE can be set by whoever calls this file
# e.g., `make KCOMPILE=xxxxx`
KCOMPILE ?= ../../../tools/kompile.pl

# this is the name of the main maude module 
LANGUAGE_NAME = EXP-UNTYPED

# this are all interesting modules (used to latexify)
LANGUAGE_MODULES = EXP-SYNTAX EXP-UNTYPED-DESUGARED-SYNTAX EXP-UNTYPED-SEMANTICS

#this is the basename of the main file
MAIN_FILE = exp-untyped

# this is a space-separated list of basename maude files to run
TESTS = exp-untyped-test.m

TOOL_DIR = $(dir $(KCOMPILE))
include $(TOOL_DIR)make-helper.mk
