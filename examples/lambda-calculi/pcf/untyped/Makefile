# KCOMPILE can be set by whoever calls this file
# e.g., `make KCOMPILE=xxxxx`
KCOMPILE ?= ../../../../tools/kompile.pl

# this is the name of the main maude module 
LANGUAGE_NAME = PCF-UNTYPED

# this are all interesting modules (used to latexify)
LANGUAGE_MODULES = PCF-UNTYPED-SYNTAX PCF-UNTYPED-SEMANTICS PCF-UNTYPED-PROGRAMS PCF-UNTYPED

LATEX_STYLE = bb

#this is the basename of the main file
MAIN_FILE = pcf-untyped

# this is a space-separated list of maude files to run
TESTS = pcf-untyped-test.m

TOOL_DIR = $(dir $(KCOMPILE))
include $(TOOL_DIR)make-helper.mk
