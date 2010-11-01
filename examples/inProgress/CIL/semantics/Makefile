K-MAUDE-BASE = ../../..
K-COMPILE-BASE = tools/kcompileFast.sh
K-PROGRAM-COMPILE = $(K-MAUDE-BASE)/tools/kcompile-program.sh

K-MAUDE = $(K-MAUDE-BASE)/$(K-COMPILE-BASE)
K-PRELUDE = $(K-MAUDE-BASE)/k-prelude
K-PL-BUILTINS = $(K-MAUDE-BASE)/pl-builtins

ADDITIONAL_SYNTAX = "including MATCH-C-SYNTAX ."

PROGRAM_BASE_NAMES = $(foreach var,$(INPUT), $(notdir $(subst .gen.maude,,$(var))))
PROGRAM_NAMES = $(foreach var, $(PROGRAM_BASE_NAMES), program-$(var))
PROGRAM_DIR = ../programs
PROGRAM_TARGET = $(foreach var, $(PROGRAM_BASE_NAMES), program-$(var)-compiled.maude)
PROGRAM_TARGET_NO_MAUDE = $(foreach var, $(PROGRAM_BASE_NAMES), program-$(var)-compiled)
COMPILED_PROGRAM_LOADS = `echo -e "$(foreach var, $(PROGRAM_TARGET_NO_MAUDE), load $(var) .\n)"`


.PHONY: all clean force check-input dynamic match semantics

.SECONDARY:

all: dynamic 

check-input: 
ifeq ($(INPUT),)
	exit 1
endif
	
c-syntax.maude: Makefile
	@printf "`cat c-syntax.template`" $(ADDITIONAL_SYNTAX) > c-syntax.maude	
	
c.maude: c-syntax.maude c-maude.template Makefile
	@printf "`cat c-maude.template`" $(K-PRELUDE) $(CONFIGURATION_FILE) $(SEMANTICS_FILE) $(SEMANTICS_MODULE) > c.maude
	
c-compiled.maude: c.maude $(K-MAUDE) \
common-c-syntax.maude common-c-configuration.maude common-c-semantics.maude common-c-standard-lib.maude common-c-expressions.maude common-c-statements.maude common-c-conversions.maude common-c-typing.maude \
match-c-syntax.maude match-c-semantics.maude match-c-configuration.maude \
dynamic-c-semantics.maude dynamic-c-configuration.maude
	$(K-MAUDE) c.maude C
	
c-total.maude: c-compiled.maude $(K-PRELUDE).maude $(K-PL-BUILTINS).maude
#echo adds a newline
	@echo | cat c-compiled.maude c-syntax.maude - common-c-configuration.maude | perl slurp.pl ./ > c-total.maude
	
dynamic-test: dynamic test.maude

match-test: match test.maude

dynamic: SEMANTICS_MODULE = "DYNAMIC-C-SEMANTICS" 
dynamic: SEMANTICS_FILE = "dynamic-c-semantics"
dynamic: CONFIGURATION_FILE = "dynamic-c-configuration"
dynamic: semantics

match: SEMANTICS_MODULE = "MATCH-C-SEMANTICS"
match: SEMANTICS_FILE = "match-c-semantics"
match: CONFIGURATION_FILE = "match-c-configuration"
match: semantics

semantics: c-total.maude

clean:
	rm -f program-*-gen.maude program-*-compiled.maude program-*-compiled.maude.tmp c-syntax.maude c-compiled.maude c.maude test.maude programs-gen.maude test-benchmark.maude kcompile_* quoted.maude c-total.maude

force: ;
