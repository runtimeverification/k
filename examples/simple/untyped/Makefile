# KCOMPILE can be set by whoever calls this file
# e.g., `make KCOMPILE=xxxxx`
KCOMPILE ?= $(shell which kompile)

# this is the name of the main maude module 
LANGUAGE_NAME = SIMPLE-UNTYPED

# this are all interesting modules (used to latexify)
LANGUAGE_MODULES = SIMPLE-UNTYPED-SYNTAX SIMPLE-UNTYPED-DESUGARED-SYNTAX SIMPLE-UNTYPED-SEMANTICS SIMPLE-UNTYPED

LATEX_STYLE = bb
LATEX_TOPMATTER = README.tex

#this is the basename of the main file
MAIN_FILE = simple-untyped

# this is a space-separated list of basename maude files to run
TESTS = simple-untyped-test.m

TOOL_DIR = $(dir $(KCOMPILE))
include $(TOOL_DIR)make-helper.mk
