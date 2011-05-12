# KCOMPILE can be set by whoever calls this file
# e.g., `make KCOMPILE=xxxxx`
KCOMPILE ?= $(shell which kompile)

# this is the name of the main maude module 
LANGUAGE_NAME = SIMPLY-SUBTYPED

# this are all interesting modules (used to latexify)
LANGUAGE_MODULES = SIMPLY-SUBTYPED-SYNTAX SIMPLY-SUBTYPED-SEMANTICS SIMPLY-SUBTYPED-PROGRAMS SIMPLY-SUBTYPED

LATEX_STYLE = bb

#this is the basename of the main file
MAIN_FILE = simply-subtyped

# this is a space-separated list of basename maude files to run
TESTS =

TOOL_DIR = $(dir $(KCOMPILE))
include $(TOOL_DIR)make-helper.mk
