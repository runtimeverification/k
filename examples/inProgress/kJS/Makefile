# KCOMPILE can be set by whoever calls this file
# e.g., `make KCOMPILE=xxxxx`
KCOMPILE ?= ../../../tools/kompile.pl

# this is the name of the main maude module 
LANGUAGE_NAME = JS

# this is the name of the interesting modules (used by make latex/pdf) 
LANGUAGE_MODULES = JS JS-CONFIGURATION 

#this is the basename of the main file
MAIN_FILE = js

# this is a space-separated list of basename maude files to run
TESTS = js-unit-tests.m

TOOL_DIR = $(dir $(KCOMPILE))
include $(TOOL_DIR)make-helper.mk
