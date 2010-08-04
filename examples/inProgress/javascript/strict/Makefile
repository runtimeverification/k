# KCOMPILE can be set by whoever calls this file
# e.g., `make KCOMPILE=xxxxx`
KCOMPILE ?= ../../../../tools/kompile.pl

# this is the name of the main maude module 
LANGUAGE_NAME = STRICT-JAVASCRIPT

# this is the name of the interesting modules (used by make latex/pdf) 
LANGUAGE_MODULES = STRICT-JAVASCRIPT-SYNTAX STRICT-JAVASCRIPT-PROGRAMS STRICT-JAVASCRIPT-SEMANTICS STRICT-JAVASCRIPT

#this is the basename of the main file
MAIN_FILE = strict-javascript

# this is a space-separated list of basename maude files to run
TESTS = strict-javascript-test.m

TOOL_DIR = $(dir $(KCOMPILE))
include $(TOOL_DIR)make-helper.mk
