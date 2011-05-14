# KCOMPILE can be set by whoever calls this file
# e.g., `make KCOMPILE=xxxxx`
KCOMPILE ?= $(K_CORE)/kompile

# this is the name of the main maude module 
LANGUAGE_NAME = ISSUE039

# this is the name of the interesting modules (used by make latex/pdf) 
LANGUAGE_MODULES = ISSUE039

#this is the basename of the main file
MAIN_FILE = issue039

# this is a space-separated list of basename maude files to run
TESTS = test.m

TOOL_DIR = $(dir $(KCOMPILE))../tools/
include $(TOOL_DIR)make-helper.mk
