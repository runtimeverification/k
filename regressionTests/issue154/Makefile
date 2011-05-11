# KCOMPILE can be set by whoever calls this file
# e.g., `make KCOMPILE=xxxxx`
KCOMPILE ?= ../../tools/kompile

# this is the name of the main maude module 
LANGUAGE_NAME = ISSUE154

# this is the name of the interesting modules (used by make latex/pdf) 
LANGUAGE_MODULES = ISSUE154

#this is the basename of the main file
MAIN_FILE = example

# this is a space-separated list of basename maude files to run
TESTS =

TOOL_DIR = $(dir $(KCOMPILE))
include $(TOOL_DIR)make-helper.mk
