# KCOMPILE can be set by whoever calls this file
# e.g., `make KCOMPILE=xxxxx`
KCOMPILE ?= ../../../tools/kompile.pl

# this is the name of the main maude module 
LANGUAGE_NAME = META-MODEL

# this are all interesting modules (used to latexify)
#LANGUAGE_MODULES = 

LATEX_STYLE = bb

# this is the basename of the main file
MAIN_FILE = dsml

# these are additional files that when changed will force rebuilding the semantics
#ADDITIONAL_DEPENDENCIES = 

# this is a space-separated list of basename maude files to run
#TESTS =  

TOOL_DIR = $(dir $(KCOMPILE))
include $(TOOL_DIR)make-helper.mk

