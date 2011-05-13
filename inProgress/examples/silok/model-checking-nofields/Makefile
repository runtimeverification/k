# KCOMPILE can be set by whoever calls this file
# e.g., `make KCOMPILE=xxxxx`
KCOMPILE ?= $(shell which kompile)

# this is the name of the main maude module 

LANGUAGE_NAME = SILOK-ABSTRACT-SEMANTICS-AS-FINITE-MODEL
#LANGUAGE_NAME = SILOK-ABSTRACT-SEMANTICS


# this are all interesting modules (used to latexify)

LANGUAGE_MODULES = SILOK-SYNTAX SILOK-ABSTRACT-SEMANTICS-AS-FINITE-MODEL 
#LANGUAGE_MODULES = SILOK-SYNTAX SILOK-ABSTRACT-SEMANTICS

LATEX_STYLE = bb

# this is the basename of the main file
MAIN_FILE = silok-abstract-semantics-as-finite-model
#MAIN_FILE = silok-abstract-semantics

# these are additional files that when changed will force rebuilding the semantics
#ADDITIONAL_DEPENDENCIES = 

# this is a space-separated list of basename maude files to run
# TESTS =  test.maude


TOOL_DIR = $(dir $(KCOMPILE))
include $(TOOL_DIR)make-helper.mk

