#COMPILE_OPTIONS = -supercool local -superheat nerd

# this is the name of the main maude module 
LANGUAGE_NAME = EXAMPLE

# this is the name of the interesting modules (used by make latex/pdf) 
LANGUAGE_MODULES = EXAMPLE

#this is the basename of the main file
MAIN_FILE = example

# this is a space-separated list of basename maude files to run
#TESTS = test.m

# this is a space separated list of directories containing io_tests
IO_TESTS = programs/tests
# this is the name the tests will be grouped under
IO_TESTSUITE_NAME = $(MAIN_FILE)
# this is a flag used when calling krun to be used when doing io_tests
IO_TEST_FLAG = "--no-color --output-mode=pretty"

TOOL_DIR =  $(K_BASE)/tools/
include $(TOOL_DIR)make-helper.mk
