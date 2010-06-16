# KCOMPILE can be set by whoever calls this file
# e.g., `make KCOMPILE=xxxxx`
KCOMPILE ?= ../../../../tools/kompile.pl

# this is the name of the main maude module 
LANGUAGE_NAME = SIMPLE-TYPED-STATIC

#this is the basename of the main file
MAIN_FILE = simple-typed-static

# this is a space-separated list of basename maude files to run
TESTS = simple-typed-static-test.maude

TOOL_DIR = $(dir $(KCOMPILE))
include $(TOOL_DIR)make-helper.mk
	
