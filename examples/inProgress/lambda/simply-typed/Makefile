# KCOMPILE can be set by whoever calls this file
# e.g., `make KCOMPILE=xxxxx`
KCOMPILE ?= ../../../../tools/kompile.pl

# this is the name of the main maude module 
LANGUAGE_NAME = SIMPLY-TYPED-LAMBDA

# this are all interesting modules (used to latexify)
LANGUAGE_MODULES = K-VISITOR SUBSTITUTION SIMPLY-TYPED-SEMANTICS

#this is the basename of the main file
MAIN_FILE = simply-typed-lambda

# this is a space-separated list of basename maude files to run
TESTS = simply-typed-lambda-test.m

TOOL_DIR = $(dir $(KCOMPILE))
include $(TOOL_DIR)make-helper.mk
