C_DIR = programs
SEMANTICS_DIR = semantics
PARSER_DIR = parser
PARSER = $(PARSER_DIR)/cparser
DIST_DIR = dist
OUTPUT_FILTER_DIR = ../../../tools/OutputFilter
OUTPUT_FILTER = $(OUTPUT_FILTER_DIR)/filterOutput
FILTER = $(SEMANTICS_DIR)/outputFilter.yml
#VPATH = programs

FILES_TO_DIST = \
	$(SEMANTICS_DIR)/c-total.maude \
	$(SEMANTICS_DIR)/compile.sh \
	$(SEMANTICS_DIR)/slurp.pl \
	$(SEMANTICS_DIR)/wrapper.pl \
	$(SEMANTICS_DIR)/link.pl \
	$(PARSER_DIR)/cparser \
	$(C_DIR)/compileProgram.sh \
	$(C_DIR)/embed.pl \
	$(wildcard $(C_DIR)/includes/*) \
	$(wildcard $(C_DIR)/lib/*)

	
.PHONY: all clean run test force cparser maude-fragments build-all dynamic match fix kcompile gcc-output kcompile-bench benchmark dist fast-test dist-make

all: cparser

dist: $(DIST_DIR)/dist.done

demo: $(DIST_DIR)/dist.done 
	@rm -f ./a.out
#$(DIST_DIR)/kcc -o ./a.out -d -s $(C_DIR)/c1x-6-7-8.c
#$(DIST_DIR)/kcc -o ./a.out -s -d tests/unitTests/tesetQualifiers.c
#$(DIST_DIR)/kcc -o ./a.out -s $(C_DIR)/twoFile1.c $(C_DIR)/twoFile2.c
#@DEBUG=1 ./a.out
	$(DIST_DIR)/kcc -d -s -o ./a.out programs/base64.c
	@DEBUG=1 ./a.out
# $(DIST_DIR)/kcc -o ./a.out -d -s $(C_DIR)/challenge03.c
# ./a.out	
# $(DIST_DIR)/kcc -o ./a.out -d -s $(C_DIR)/challenge04.c
# ./a.out	
# $(DIST_DIR)/kcc -o ./a.out -d -s $(C_DIR)/challenge05.c
# ./a.out	
# $(DIST_DIR)/kcc -o ./a.out -d -s $(C_DIR)/schorr-waite.c
# ./a.out
# $(DIST_DIR)/kcc -o ./a.out -d -s $(C_DIR)/globals.c
# @./a.out
# $(DIST_DIR)/kcc -o ./a.out -d -s $(C_DIR)/arr.c
# @./a.out
# $(DIST_DIR)/kcc -o ./a.out -d -s $(C_DIR)/arithConversions.c
# @./a.out
# $(DIST_DIR)/kcc -o ./a.out -d -s $(C_DIR)/differentInits.c
# @./a.out

#$(DIST_DIR)/dist.tested

filter: $(OUTPUT_FILTER)

$(OUTPUT_FILTER): $(wildcard $(OUTPUT_FILTER_DIR)/*.hs)
	make -C $(OUTPUT_FILTER_DIR)

$(DIST_DIR)/dist.done: Makefile filter cparser kcompile $(FILES_TO_DIST)
	@mkdir -p $(DIST_DIR)
	@mkdir -p $(DIST_DIR)/includes
	@mkdir -p $(DIST_DIR)/lib
	@cp $(FILES_TO_DIST) $(DIST_DIR)
	@cp $(OUTPUT_FILTER) $(DIST_DIR)
	@cp $(FILTER) $(DIST_DIR)
	@mv $(DIST_DIR)/*.h $(DIST_DIR)/includes
	@mv $(DIST_DIR)/clib.c $(DIST_DIR)/lib
#@ln -s -f compile.sh $(DIST_DIR)/kcc
	@mv $(DIST_DIR)/compile.sh $(DIST_DIR)/kcc
	@$(DIST_DIR)/kcc -c -o $(DIST_DIR)/lib/clib.o $(DIST_DIR)/lib/clib.c
	@touch $(DIST_DIR)/dist.done

$(DIST_DIR)/dist.tested: $(DIST_DIR)/dist.done 
	@make -C $(C_DIR) fast-test
	@touch $(DIST_DIR)/dist.tested
	
test: dist
	@make -C tests

integration-test:
	@make -C tests integration
	
unit-test:
	@make -C tests unit
	
torture-test:
	@make -C tests torture
	
thirdParty-test:
	@make -C tests thirdParty
	
fix: 
	maude $(SEMANTICS_DIR)/programs-gen.maude
fixnew:
	maude $(SEMANTICS_DIR)/kcompile_in.maude

force: ;

cparser:
	@make -C $(PARSER_DIR)

kcompile:
	@make -C $(SEMANTICS_DIR) dynamic

benchmark: profile.csv

profile.csv: profile.log
	perl analyzeProfile.pl > profile.csv

clean:
	make -C $(C_DIR) clean
	make -C $(PARSER_DIR) clean
	make -C $(SEMANTICS_DIR) clean
	make -C gcc-test clean
	make -C tests clean
	rm -rf $(DIST_DIR)
	rm -f ./*.tmp ./*.log ./*.cil ./*-gen.maude ./*.gen.maude ./*.pre.gen ./*.prepre.gen ./a.out
