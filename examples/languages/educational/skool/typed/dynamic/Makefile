# KCOMPILE can be set by whoever calls this file
# e.g., `make KCOMPILE=xxxxx`
KCOMPILE ?= $(shell which kompile)

# this is the name of the main maude module 
LANGUAGE_NAME = SKOOL-TYPED-DYNAMIC

# this are all interesting modules (used to latexify)
LANGUAGE_MODULES = SKOOL-TYPED-SYNTAX SKOOL-TYPED-DYNAMIC-DESUGARED-SYNTAX SKOOL-TYPED-DYNAMIC-SEMANTICS SKOOL-TYPED-DYNAMIC

LATEX_STYLE = bb

#this is the basename of the main file
MAIN_FILE = skool-typed-dynamic

# these are additional files that when changed will force rebuilding the semantics
ADDITIONAL_DEPENDENCIES = ../skool-typed-programs.k

# this is a space-separated list of basename maude files to run
TESTS = skool-typed-dynamic-test.m

TOOL_DIR = $(dir $(KCOMPILE))../tools/
include $(TOOL_DIR)make-helper.mk

