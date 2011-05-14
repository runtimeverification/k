# KCOMPILE can be set by whoever calls this file
# e.g., `make KCOMPILE=xxxxx`
KCOMPILE ?= $(shell which kompile)

# this is the name of the main maude module 
LANGUAGE_NAME = KERNELC

# this are all interesting modules (used to latexify)
LANGUAGE_MODULES = KERNELC-SYNTAX KERNELC-THREADS-SYNTAX KERNELC-DESUGARED-SYNTAX KERNELC-SEMANTICS  KERNELC-SIMPLE-MALLOC  KERNELC-CONSISTENT-MEMORY KERNELC-CONSISTENT-THREADS KERNELC

LATEX_TOPMATTER = README.tex

#this is the basename of the main file
MAIN_FILE = kernelc

# this is a space-separated list of basename maude files to run
TESTS = kernelc-test.m

TOOL_DIR = $(dir $(KCOMPILE))
include $(TOOL_DIR)make-helper.mk
