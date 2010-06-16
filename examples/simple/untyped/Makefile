# KCOMPILE can be set by whoever calls this file
# e.g., `make KCOMPILE=xxxxx`
KCOMPILE ?= ../../../tools/kompile.pl

# this is the name of the main maude module 
LANGUAGE_NAME = SIMPLE-UNTYPED

#this is the basename of the main file
MAIN_FILE = simple-untyped

# this is a space-separated list of basename maude files to run
TESTS = simple-untyped-test.m

TOOL_DIR = $(dir $(KCOMPILE))
include $(TOOL_DIR)make-helper.mk
	
