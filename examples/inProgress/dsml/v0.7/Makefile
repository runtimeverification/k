# KCOMPILE can be set by whoever calls this file
# e.g., `make KCOMPILE=xxxxx`
KCOMPILE ?= ../../../../tools/kompile

# this is the name of the main maude module 

# LANGUAGE_NAME = OCL-SYNTAX
# LANGUAGE_NAME = META-MODEL
# LANGUAGE_NAME = OCL-SEMANTICS
 LANGUAGE_NAME = TEST

# this are all interesting modules (used to latexify)
#LANGUAGE_MODULES = 

LATEX_STYLE = bb

# this is the basename of the main file
# MAIN_FILE = ocl-syntax
# MAIN_FILE = meta-model
# MAIN_FILE = ocl-semantics
 MAIN_FILE = test

# these are additional files that when changed will force rebuilding the semantics
#ADDITIONAL_DEPENDENCIES = 

# this is a space-separated list of basename maude files to run
# TESTS =  test-ocl.maude


TOOL_DIR = $(dir $(KCOMPILE))
include $(TOOL_DIR)make-helper.mk

