# KCOMPILE can be set by whoever calls this file
# e.g., `make KCOMPILE=xxxxx`
KCOMPILE ?= ../../../../../tools/kompile.pl

# this is the name of the main maude module 

 LANGUAGE_NAME = AUTOMATA

# this are all interesting modules (used to latexify)
LANGUAGE_MODULES = OCL-SYNTAX META-MODEL OCL-SEMANTICS

LATEX_STYLE = bb


 MAIN_FILE = automata

# these are additional files that when changed will force rebuilding the semantics
#ADDITIONAL_DEPENDENCIES = 

# this is a space-separated list of basename maude files to run
# TESTS =  test-ocl.maude


TOOL_DIR = $(dir $(KCOMPILE))
include $(TOOL_DIR)make-helper.mk

