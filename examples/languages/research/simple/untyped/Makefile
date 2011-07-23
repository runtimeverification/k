
# this is the name of the main maude module 
LANGUAGE_NAME = SIMPLE-UNTYPED

# this are all interesting modules (used to latexify)
LANGUAGE_MODULES = SIMPLE-UNTYPED-SYNTAX SIMPLE-UNTYPED-DESUGARED-SYNTAX SIMPLE-UNTYPED-SEMANTICS SIMPLE-UNTYPED

LATEX_STYLE = bb
LATEX_TOPMATTER = README.tex

#this is the basename of the main file
MAIN_FILE = simple-untyped

COMPILE_OPTIONS = -transition "nondet nd" -supercool "nondet"

# this is a space-separated list of basename maude files to run
TESTS = simple-untyped-test.m

TOOL_DIR =  $(K_BASE)/tools/
include $(TOOL_DIR)make-helper.mk
