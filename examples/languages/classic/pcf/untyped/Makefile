# this is the name of the main maude module 
LANGUAGE_NAME = PCF-UNTYPED

# this are all interesting modules (used to latexify)
LANGUAGE_MODULES = PCF-UNTYPED-SYNTAX PCF-UNTYPED-SEMANTICS PCF-UNTYPED

LATEX_STYLE = bubble
LATEX_TOPMATTER = topmatter.tex

#this is the basename of the main file
MAIN_FILE = pcf-untyped

# this is a space-separated list of maude files to run
TESTS = pcf-untyped-test.m

# this is a space separated list of directories containing io_tests
IO_TESTS = programs/tests
# this is the name the tests will be grouped under
IO_TESTSUITE_NAME = $(MAIN_FILE)
# this is a flag used when calling krun to be used when doing io_tests
IO_TEST_FLAG = "--no-color --output-mode=pretty"

TOOL_DIR =  $(K_BASE)/tools/
include $(TOOL_DIR)make-helper.mk
