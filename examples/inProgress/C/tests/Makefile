COMMAND_PREFIX = nice -n 19
# i feel like this is in danger of messing up tests
#COMMAND_PREFIX =

KCC ?= ../dist/compile.sh
GCC ?= gcc -lm -Wall -Wextra -x c -O0 -U __GNUC__ -pedantic -std=c99
#-Werror 
PARSER ?= ../dist/cparser

GOOD_DIRECTORIES = unitTests
FAIL_DIRECTORIES = shouldFail
INTEGRATION_DIRECTORIES = integration
ALL_DIRECTORIES = $(GOOD_DIRECTORIES) $(FAIL_DIRECTORIES) $(INTEGRATION_DIRECTORIES)

#ALL_FILES = $(foreach var, $(GOOD_DIRECTORIES), $(wildcard $(var)/*.c))
#ALL_PROGRAMS_BASIC = $(basename $(ALL_FILES))
#ALL_PROGRAMS = $(filter-out $(DONT_WORK), $(ALL_PROGRAMS_BASIC))
#ALL_TARGETS = $(foreach var,  $(filter-out $(DONT_RUN), $(ALL_PROGRAMS)), $(dir $(var))compare-$(notdir $(var)).pass)
GOOD_TARGETS = $(foreach var,  $(GOOD_DIRECTORIES), results-pass-$(var).xml)
FAIL_TARGETS = $(foreach var,  $(FAIL_DIRECTORIES), results-fail-$(var).xml)
INTEGRATION_TARGETS = $(foreach var, $INTEGRATION_DIRECTORIES), results-pass-$(var).xml)
CLEAN_TARGETS = $(foreach var, $(ALL_DIRECTORIES), clean-$(var))

all: $(PARSER) test 

integration: $(INTEGRATION_TARGETS)

#.INTERMEDIATE: test-%.kcc test-%.gcc output-% retval-%
#.PRECIOUS: test-%.kcc test-%.gcc output-% retval-% compare-%.pass
.PHONY: all test clean good fail clean-%

test: good fail
	@echo "Tests finished running."
	
good: $(GOOD_TARGETS)

fail: $(FAIL_TARGETS)

results-pass-%.xml:
	@perl runtest.pl -p $*
	
results-fail-%.xml:
	@perl runtest.pl -f $*
		
clean: $(CLEAN_TARGETS) clean-./
	
clean-%:
	rm -f ./$*/*.gcc ./$*/*.kcc ./$*/*.pass ./$*/*.tmp ./$*/*.log ./$*/*.cil ./$*/*-gen.maude ./$*/*.gen.maude ./$*/*.pre.gen ./$*/*.prepre.gen ./$*/*.xml ./$*/a.out
