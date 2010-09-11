COMMAND_PREFIX = nice -n 19
# i feel like this is in danger of messing up tests
#COMMAND_PREFIX =

KCC ?= ../dist/compile.sh
GCC ?= gcc -lm -Wall -Wextra -x c -O0 -U __GNUC__ -pedantic -std=c99
#-Werror 
PARSER ?= ../dist/cparser

GOOD_DIRECTORIES = unitTests
SHOULD_FAIL = 

ALL_FILES = $(foreach var, $(GOOD_DIRECTORIES), $(wildcard $(var)/*.c))
ALL_PROGRAMS_BASIC = $(basename $(ALL_FILES))
ALL_PROGRAMS = $(filter-out $(DONT_WORK), $(ALL_PROGRAMS_BASIC))
ALL_TARGETS = $(foreach var,  $(filter-out $(DONT_RUN), $(ALL_PROGRAMS)), $(dir $(var))compare-$(notdir $(var)).pass)

all: test $(PARSER)

.INTERMEDIATE: test-%.kcc test-%.gcc output-% retval-%
.PRECIOUS: test-%.kcc test-%.gcc output-% retval-% compare-%.pass

.PHONY: all test clean prepare fast-test working

test: $(ALL_TARGETS)
	@echo "SUCCESS: Tests completed successfully."

fast-test: $(FAST_TARGETS)
	@echo "SUCCESS: Tests completed successfully."

slow-test: $(SLOW_TARGETS) $(ALL_TARGETS) 
	@echo "SUCCESS: Tests completed successfully."

test-%.kcc: %.c $(KCC) $(PARSER)
	@echo "Compiling $@..."
	@$(COMMAND_PREFIX) $(KCC) -o $@ $<
	
test-%.gcc: %.c
	@echo "Compiling $@..."
	@$(GCC) -o $@ $< 2> /dev/null
	
output-%: test-%
	@echo "Running $< ..."
	@trap "" SIGABRT; $(COMMAND_PREFIX) ./$< 2>&1 > $@.tmp; RETURN_VALUE=$$?; echo $$RETURN_VALUE >> $@.tmp
	@mv $@.tmp $@
	
compare-%.pass: output-%.gcc output-%.kcc
	@echo "Comparing $*..."
	@diff -y --suppress-common-lines -I '^VOLATILE' $+
	@touch $@
		
clean:
#rm -f *.gcc *.kcc *.tmp *.pass *-information.log compilation.log *-gen.maude *.pre.gen *.prepre.gen *.gen.maude a.out kcompile_* program-*-compiled.maude *.o *.cil
	rm -f ./*.gcc ./*.kcc ./*.pass ./*.tmp ./*.log ./*.cil ./*-gen.maude ./*.gen.maude ./*.pre.gen ./*.prepre.gen ./a.out
