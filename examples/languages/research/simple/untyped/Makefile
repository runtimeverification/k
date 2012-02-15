
# this is the name of the main maude module 
LANGUAGE_NAME = SIMPLE-UNTYPED

# this are all interesting modules (used to latexify)
LANGUAGE_MODULES = SIMPLE-UNTYPED-SYNTAX SIMPLE-UNTYPED

LATEX_STYLE = bubble
LATEX_TOPMATTER = README.tex

#this is the basename of the main file
MAIN_FILE = simple-untyped

# this is a space-separated list of basename maude files to run
TESTS = 

# this is a space separated list of directories containing io_tests
IO_TESTS = programs/diverse/tests
# this is the name the tests will be grouped under
IO_TESTSUITE_NAME = $(MAIN_FILE)
# this is a flag used when calling krun to be used when doing io_tests
IO_TEST_FLAG = "--output-mode=none"

TOOL_DIR =  $(K_BASE)/tools/
include $(TOOL_DIR)make-helper.mk
