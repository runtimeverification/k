# KCOMPILE can be set by whoever calls this file
# e.g., `make KCOMPILE=xxxxx`
KCOMPILE ?= ../../tools/kcompile.sh

# this is the name of the main maude module 
LANGUAGE_NAME = IMPPP

#this is the basename of the main file
MAIN_FILE = imppp

# this is a space-separated list of basename maude files to run
TESTS = imppp-test


################################
# You shouldn't need to change anything below here.
# The things below are set based on what you set above
COMPILED_FILE = $(MAIN_FILE)-compiled.maude
LANGUAGE_FILE = $(MAIN_FILE).maude

# phony tells make which targets aren't real files
.PHONY: all test-% test force

# the top target, so the default target
# compiles the definition, then runs all of the tests
all: test

# this just builds the $(COMPILED_FILE) by running $(KCOMPILE)
$(COMPILED_FILE): $(LANGUAGE_FILE) force
	$(KCOMPILE) $(LANGUAGE_FILE) $(LANGUAGE_NAME)

# to satisfy the target "test", it needs to satisfy the targets "test-a test-b test-c" for a b c \in $(TESTS)
test: $(COMPILED_FILE) $(addprefix test-,$(TESTS))

# this is how to satisfy the target "test-%" for some %.  It requires %.maude to exist.  It then runs it through maude
test-%: %.maude
	echo q | maude $<

# used to force targets to run
force: ;
	
