
# defaults, are set only if they weren't set before
KCOMPILE ?= $(K_BASE)/core/kompile
MAIN_FILE ?= yourLanguage
LANGUAGE_NAME ?= YOURLANGUAGE
SHELL = /usr/bin/env bash
################################
# You shouldn't need to change anything below here.
# The things below are set based on what you set above
# ADDITIONAL_DEPENDENCIES ?=
ALL_MAUDE_FILES = $(wildcard *.k) $(wildcard *.k) $(wildcard */*.k) $(wildcard */*/*.k) $(wildcard *.m) $(wildcard *.m) $(wildcard */*.m) $(wildcard */*/*.m)  $(wildcard *.kmaude) $(wildcard *.kmaude) $(wildcard */*.kmaude) $(wildcard */*/*.kmaude) $(wildcard *.maude) $(wildcard *.maude) $(wildcard */*.maude) $(wildcard */*/*.maude)
MAUDE_FILES = $(filter-out %-compiled.maude,$(ALL_MAUDE_FILES))
TOOL_DIR_FILES = $(wildcard $(TOOL_DIR)/*)
COMPILED_FILE = $(MAIN_FILE)-compiled.maude
# LATEX_FILE = $(MAIN_FILE).tex
# DVI_FILE = $(MAIN_FILE).DVI
# PDF_FILE = $(MAIN_FILE).pdf
# CROP_PDF_FILE = $(MAIN_FILE)-crop.pdf
# EPS_FILES = $(MAIN_FILE)-ps-001.eps
# PNG_FILES = $(EPS_FILES).png
LATEX_STYLE ?= bb
LANGUAGE_FILE = $(or $(shell if [ -e $(MAIN_FILE).k ]; then echo $(MAIN_FILE).k; fi), $(or $(shell if [ -e $(MAIN_FILE).kmaude ]; then echo $(MAIN_FILE).kmaude; fi), $(shell if [ -e $(MAIN_FILE).maude ]; then echo $(MAIN_FILE).maude; fi)))

COMPILE_OPTIONS ?= $(DRAFT)

ifdef LATEX_TOPMATTER
  LATEX_EXTRA_ARGS += -topmatter $(LATEX_TOPMATTER)
endif
ifdef LATEX_DRAFT
  LATEX_EXTRA_ARGS += -draft
endif

# phony tells make which targets aren't real files
.PHONY: all test-% test force build

# the top target, so the default target
# compiles the definition, then runs all of the tests
all: build 

build: $(COMPILED_FILE)

# this just builds the $(COMPILED_FILE) by running $(KCOMPILE)
$(COMPILED_FILE): $(LANGUAGE_FILE) $(TOOL_DIR_FILES) $(MAUDE_FILES) $(ADDITIONAL_DEPENDENCIES) Makefile
	$(KCOMPILE) $(LANGUAGE_FILE) $(COMPILE_OPTIONS) -l $(LANGUAGE_NAME) 2>&1 |tee $(COMPILED_FILE).output && exit $${PIPESTATUS[0]}

# this should build the latex
latex: $(LANGUAGE_FILE) $(TOOL_DIR_FILES) $(MAUDE_FILES) Makefile
	$(KCOMPILE) $(LANGUAGE_FILE) -l $(LANGUAGE_NAME) -style $(LATEX_STYLE) -latex $(LANGUAGE_MODULES) $(LATEX_EXTRA_ARGS)

# this should build the pdf
pdf:  $(LANGUAGE_FILE) $(TOOL_DIR_FILES) $(MAUDE_FILES) Makefile
	$(KCOMPILE) $(LANGUAGE_FILE) -l $(LANGUAGE_NAME) -style $(LATEX_STYLE) -pdf $(LANGUAGE_MODULES) $(LATEX_EXTRA_ARGS)

# this should build the pdf in draft mode
pdfdraft:  $(LANGUAGE_FILE) $(TOOL_DIR_FILES) $(MAUDE_FILES) Makefile
	$(KCOMPILE) $(LANGUAGE_FILE) -l $(LANGUAGE_NAME) -style $(LATEX_STYLE) -pdf $(LANGUAGE_MODULES) $(LATEX_EXTRA_ARGS) -draft

# this should build the png
png:  $(LANGUAGE_FILE) $(TOOL_DIR_FILES) $(MAUDE_FILES) Makefile
	$(KCOMPILE) $(LANGUAGE_FILE) -l $(LANGUAGE_NAME) -style $(LATEX_STYLE) -png $(LANGUAGE_MODULES) $(LATEX_EXTRA_ARGS)

# this should build the eps
eps:  $(LANGUAGE_FILE) $(TOOL_DIR_FILES) $(MAUDE_FILES) Makefile
	$(KCOMPILE) $(LANGUAGE_FILE) -l $(LANGUAGE_NAME) -style $(LATEX_STYLE) -eps $(LANGUAGE_MODULES) $(LATEX_EXTRA_ARGS)

# this should build the ps
ps:  $(LANGUAGE_FILE) $(TOOL_DIR_FILES) $(MAUDE_FILES) Makefile
	$(KCOMPILE) $(LANGUAGE_FILE) -l $(LANGUAGE_NAME) -style $(LATEX_STYLE) -ps $(LANGUAGE_MODULES) $(LATEX_EXTRA_ARGS)

# this should build the crop-pdf
crop-pdf:  $(LANGUAGE_FILE) $(TOOL_DIR_FILES) $(MAUDE_FILES) Makefile
	$(KCOMPILE) $(LANGUAGE_FILE) -l $(LANGUAGE_NAME) -style $(LATEX_STYLE) -crop $(LANGUAGE_MODULES) $(LATEX_EXTRA_ARGS)


# to satisfy the target "test", it needs to satisfy the targets "test-a test-b test-c" for a b c \in $(TESTS)
test: $(COMPILED_FILE) $(addprefix test-,$(addsuffix .output,$(TESTS)))

true-test: $(COMPILED_FILE) $(foreach test, $(TESTS), results-$(test).xml) compilation.xml

# this is how to satisfy the target "test-%" for some %.  It requires file % to exist.  It then runs it through maude
test-%.output: % $(COMPILED_FILE) 
	@echo q | maude -no-wrap -no-ansi-color $< 2>&1 |tee $@ && exit $${PIPESTATUS[0]}
#@cat $@
	
results-%.xml: % test-%.output
	@perl $(TOOL_DIR)/createXMLTestOutput.pl $(notdir $(realpath .)).$(basename $(notdir $*)) $* test-$*.output > $@
	
compilation.xml: $(COMPILED_FILE).output
	@perl $(TOOL_DIR)/createXMLCompilationOutput.pl $(notdir $(realpath .)).compilation $(COMPILED_FILE).output > $@
#$(COMPILED_FILE).output
	
# used to force targets to run
force: ;
	
clean:
	@-rm -f $(COMPILED_FILE) kompile_* $(MAIN_FILE).aux $(MAIN_FILE).log $(MAIN_FILE).pdf $(MAIN_FILE)-ps-* $(MAIN_FILE).dvi $(MAIN_FILE).eps $(MAIN_FILE).ps *.png $(MAIN_FILE).tex $(CROP_PDF_FILE) test-*.output shared.maude results-*.xml
	@-rm -f ${subst .k,.maude, ${filter %.k, $(LANGUAGE_FILE)}}
	@-rm -f compilation.xml $(COMPILED_FILE).output
