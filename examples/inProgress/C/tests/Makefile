COMMAND_PREFIX = nice -n 19
# i feel like this is in danger of messing up tests
#COMMAND_PREFIX =

KCC ?= ../dist/compile.sh
GCC ?= gcc -lm -Wall -Wextra -x c -O0 -U __GNUC__ -pedantic -std=c99
#-Werror 
PARSER ?= ../dist/cparser

GOOD_DIRECTORIES = unitTests
SHOULD_FAIL = 

#ALL_FILES = $(foreach var, $(GOOD_DIRECTORIES), $(wildcard $(var)/*.c))
#ALL_PROGRAMS_BASIC = $(basename $(ALL_FILES))
#ALL_PROGRAMS = $(filter-out $(DONT_WORK), $(ALL_PROGRAMS_BASIC))
#ALL_TARGETS = $(foreach var,  $(filter-out $(DONT_RUN), $(ALL_PROGRAMS)), $(dir $(var))compare-$(notdir $(var)).pass)
GOOD_TARGETS = $(foreach var,  $(GOOD_DIRECTORIES), results-$(var).xml)
CLEAN_TARGETS = $(foreach var, $(GOOD_DIRECTORIES), clean-$(var))

all: $(PARSER) test 

.INTERMEDIATE: test-%.kcc test-%.gcc output-% retval-%
.PRECIOUS: test-%.kcc test-%.gcc output-% retval-% compare-%.pass
.PHONY: all test clean prepare fast-test working

test: $(GOOD_TARGETS)
	@echo "Tests finished running."
	
results-%.xml:
	@perl runtest.pl $*
		
clean: $(CLEAN_TARGETS) clean-./
	
clean-%:
	rm -f ./$*/*.gcc ./$*/*.kcc ./$*/*.pass ./$*/*.tmp ./$*/*.log ./$*/*.cil ./$*/*-gen.maude ./$*/*.gen.maude ./$*/*.pre.gen ./$*/*.prepre.gen ./$*/*.xml ./$*/a.out
