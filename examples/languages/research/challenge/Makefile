
# this is the name of the main maude module 
LANGUAGE_NAME = CHALLENGE

# these are the interesting modules in the language (used by make latex/pdf)
LANGUAGE_MODULES = CHALLENGE-SYNTAX CHALLENGE

#this is the basename of the main file
MAIN_FILE = challenge

# this is a space-separated list of basename maude files to run
TESTS = challenge-test.m


# this is a space separated list of directories containing io_tests
IO_TESTS = programs/tests
# this is the name the tests will be grouped under
IO_TESTSUITE_NAME = $(MAIN_FILE)
# this is a flag used when calling krun to be used when doing io_tests
IO_TEST_FLAG = "--no-color --output-mode=none"

TOOL_DIR =  $(K_BASE)/tools/
include $(TOOL_DIR)make-helper.mk
