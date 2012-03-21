
# this is the name of the main maude module 
LANGUAGE_NAME = SIMPLE-TYPED-STATIC

# this are all interesting modules (used to latexify)
LANGUAGE_MODULES = SIMPLE-TYPED-STATIC-SYNTAX SIMPLE-TYPED-STATIC

LATEX_STYLE = bubble
LATEX_TOPMATTER = README.tex

#this is the basename of the main file
MAIN_FILE = simple-typed-static

# this is a space-separated list of basename maude files to run
TESTS = simple-typed-static-test.maude

# this is a space separated list of directories containing io_tests
IO_TESTS = regression/tests
# this is the name the tests will be grouped under
IO_TESTSUITE_NAME = $(MAIN_FILE)
# this is a flag used when calling krun to be used when doing io_tests
IO_TEST_FLAG = "--no-color --output-mode=none"

TOOL_DIR =  $(K_BASE)/tools/
include $(TOOL_DIR)make-helper.mk

