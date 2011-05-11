# KCOMPILE can be set by whoever calls this file
# e.g., `make KCOMPILE=xxxxx`
KCOMPILE ?= ../../../tools/kompile

# this is the name of the main maude module 
LANGUAGE_NAME = EXP-TYPE-INFERENCE

# this are all interesting modules (used to latexify)
LANGUAGE_MODULES = EXP-SYNTAX EXP-TYPE-INFERENCE-DESUGARED-SYNTAX TYPES UNIFICATION EXP-TYPE-INFERENCE-SEMANTICS

#this is the basename of the main file
MAIN_FILE = exp-type-inference

# this is a space-separated list of basename maude files to run
TESTS = exp-type-inference-test.m

TOOL_DIR = $(dir $(KCOMPILE))
include $(TOOL_DIR)make-helper.mk
