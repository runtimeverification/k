COMMAND_PREFIX = nice -n 19
# i feel like this is in danger of messing up tests
#COMMAND_PREFIX =

KCC ?= ../dist/compile.sh
GCC ?= gcc -lm -Wall -Wextra -x c -O0 -U __GNUC__ -pedantic -std=c99
#-Werror 
PARSER ?= ../dist/cparser

#GOOD_DIRECTORIES = quest
GOOD_DIRECTORIES = . fromGCC fromLCC
#GOOD_DIRECTORIES = fromGCC
#GOOD_DIRECTORIES = fromClight

DONT_WORK = ./resizeArray ./testPrintf ./badsyntax ./bigMem ./unknowns ./symbolic \
	./twoFile1 ./twoFile2 ./getchar ./sumn ./bitfields2 ./slowParse ./fileio ./hines ./testPow ./arrayOOB \
	fromGCC/pr36077 fromGCC/991118-1 \
 	fromGCC/950710-1 fromGCC/980701-1 fromGCC/loop-2d \
	fromClight/aes fromClight/almabench fromClight/bisect fromClight/binarytrees 
	
# fromGCC/pr36077 doesn't work because gcc fails
	
# 950710-1 uses pointer arithmetic regarding unrelated objects
# 980701-1 is similar, but uses result in 'if'.  it sure seems reasonable, need to check
# loop-2d does ptr arith too


# binarytrees gives wrong result.  caused by pow() underestimating some.  need to test for inputs being ints and then doing separate algorithm
	
# gcc fails pr36077
SLOW_TESTS = ./fix-fft ./quine1 ./mersenne ./md5 ./trial-division \
	fromGCC/920501-6 fromGCC/divcmp-2 fromGCC/divcmp-3 \
	fromLCC/8q
	
FAST_TESTS = ./quine2

SHOULD_FAIL = 

DONT_RUN = $(SLOW_TESTS)

# gcc -c twoFile1.c 
# gcc -c twoFile2.c 
# gcc -o a.out twoFile1.o twoFile2.o 


ALL_FILES = $(foreach var, $(GOOD_DIRECTORIES), $(wildcard $(var)/*.c))
ALL_PROGRAMS_BASIC = $(basename $(ALL_FILES))
ALL_PROGRAMS = $(filter-out $(DONT_WORK), $(ALL_PROGRAMS_BASIC))
FAST_PROGRAMS = $(filter $(FAST_TESTS), $(ALL_PROGRAMS))
SLOW_PROGRAMS = $(filter $(SLOW_TESTS), $(ALL_PROGRAMS))
ALL_TARGETS = $(foreach var,  $(filter-out $(DONT_RUN), $(ALL_PROGRAMS)), $(dir $(var))compare-$(notdir $(var)).pass)
FAST_TARGETS = $(foreach var, $(FAST_PROGRAMS), $(dir $(var))compare-$(notdir $(var)).pass)
SLOW_TARGETS = $(foreach var, $(SLOW_PROGRAMS), $(dir $(var))compare-$(notdir $(var)).pass)

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
	rm -f fromGCC/*.gcc fromGCC/*.kcc fromGCC/*.pass fromGCC/*.tmp fromGCC/*.log fromGCC/*.cil fromGCC/*-gen.maude fromGCC/*.gen.maude fromGCC/*.pre.gen fromGCC/*.prepre.gen fromGCC/a.out
	rm -f fromLCC/*.gcc fromLCC/*.kcc fromLCC/*.pass fromLCC/*.tmp fromLCC/*.log fromLCC/*.cil fromLCC/*-gen.maude fromLCC/*.gen.maude fromLCC/*.pre.gen fromLCC/*.prepre.gen fromLCC/a.out
	rm -f fromClight/*.gcc fromClight/*.kcc fromClight/*.pass fromClight/*.tmp fromClight/*.log fromClight/*.cil fromClight/*-gen.maude fromClight/*.gen.maude fromClight/*.pre.gen fromClight/*.prepre.gen fromClight/a.out
