# KCOMPILE can be set by whoever calls this file
# e.g., `make KCOMPILE=xxxxx`
KCOMPILE ?= ../../tools/kcompile.sh

# this is the name of the main maude module 
LANGUAGE_NAME = IMPPP

#this is the basename of the main file
MAIN_FILE = imppp

# this is a space-separated list of basename maude files to run
TESTS = imppp-test

TOOL_DIR = $(dir $(KCOMPILE))
include $(TOOL_DIR)make-helper.mk