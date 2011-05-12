# KCOMPILE can be set by whoever calls this file
# e.g., `make KCOMPILE=xxxxx`
KCOMPILE ?= $(shell which kompile)

# this is the name of the main maude module 

# LANGUAGE_NAME = SILOK-CONCRETE-SEMANTICS
 LANGUAGE_NAME = SILOK-ABSTRACT-SEMANTICS
# LANGUAGE_NAME = SILOK-SYMBOLIC-SEMANTICS

# this are all interesting modules (used to latexify)
# LANGUAGE_MODULES = SILOK-SYNTAX SILOK-BASIC-SEMANTICS SILOK-CONCRETE-SEMANTICS 
 LANGUAGE_MODULES = SILOK-SYNTAX SILOK-BASIC-SEMANTICS SILOK-ABSTRACT-SEMANTICS 
# LANGUAGE_MODULES = SILOK-SYNTAX SILOK-BASIC-SEMANTICS SILOK-SYMBOLIC-SEMANTICS 

LATEX_STYLE = bb

# this is the basename of the main file
# MAIN_FILE = silok-concrete-semantics
# MAIN_FILE = silok-abstract-semantics
# MAIN_FILE = silok-symbolic-semantics
# MAIN_FILE = silok-abstract-semantics-dl
 MAIN_FILE = silok-abstract-semantics-refactored

# these are additional files that when changed will force rebuilding the semantics
#ADDITIONAL_DEPENDENCIES = 

# this is a space-separated list of basename maude files to run
# TESTS =  test.maude


TOOL_DIR = $(dir $(KCOMPILE))
include $(TOOL_DIR)make-helper.mk

