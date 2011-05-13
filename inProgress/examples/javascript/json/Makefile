# KCOMPILE can be set by whoever calls this file
# e.g., `make KCOMPILE=xxxxx`
KCOMPILE ?= $(shell which kompile)

# this is the name of the main maude module 
LANGUAGE_NAME = JSON

# this is the name of the interesting modules (used by make latex/pdf) 
LANGUAGE_MODULES = JS-LIST JSON-SYNTAX JSON-PROGRAMS JSON-SEMANTICS JSON

#this is the basename of the main file
MAIN_FILE = json

# this is a space-separated list of basename maude files to run
TESTS = json-test.m

TOOL_DIR = $(dir $(KCOMPILE))
include $(TOOL_DIR)make-helper.mk
