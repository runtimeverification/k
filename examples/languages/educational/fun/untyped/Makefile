# KCOMPILE can be set by whoever calls this file
# e.g., `make KCOMPILE=xxxxx`
KCOMPILE ?= $(shell which kompile)

# this is the name of the main maude module 
LANGUAGE_NAME = FUN-UNTYPED


LANGUAGE_MODULES = FUN-SYNTAX FUN-DESUGARED-SYNTAX FUN-UNTYPED-SEMANTICS
#ADDITIONAL_DEPENDENCIES = ../fun-programs.k

#this is the basename of the main file
MAIN_FILE = fun-untyped

# this is a space-separated list of basename maude files to run
TESTS = fun-untyped-test.m

TOOL_DIR = $(dir $(KCOMPILE))../tools/
include $(TOOL_DIR)make-helper.mk
