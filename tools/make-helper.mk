################################
# You shouldn't need to change anything below here.
# The things below are set based on what you set above

ALL_MAUDE_FILES = $(wildcard *.k) $(wildcard *.k) $(wildcard */*.k) $(wildcard */*/*.k) $(wildcard *.m) $(wildcard *.m) $(wildcard */*.m) $(wildcard */*/*.m)  $(wildcard *.kmaude) $(wildcard *.kmaude) $(wildcard */*.kmaude) $(wildcard */*/*.kmaude) $(wildcard *.maude) $(wildcard *.maude) $(wildcard */*.maude) $(wildcard */*/*.maude)
MAUDE_FILES = $(filter-out %-compiled.maude,$(ALL_MAUDE_FILES))
TOOL_DIR_FILES = $(wildcard $(TOOL_DIR)/*)
COMPILED_FILE = $(MAIN_FILE)-compiled.maude
LATEX_FILE = $(MAIN_FILE).tex
PDF_FILE = $(MAIN_FILE).pdf
LATEX_STYLE ?= mm
LANGUAGE_FILE = $(or $(shell if [ -e $(MAIN_FILE).k ]; then echo $(MAIN_FILE).k; fi), $(or $(shell if [ -e $(MAIN_FILE).kmaude ]; then echo $(MAIN_FILE).kmaude; fi), $(shell if [ -e $(MAIN_FILE).maude ]; then echo $(MAIN_FILE).maude; fi)))

# phony tells make which targets aren't real files
.PHONY: all test-% test force build

# the top target, so the default target
# compiles the definition, then runs all of the tests
all: build 

build: $(COMPILED_FILE)

# this just builds the $(COMPILED_FILE) by running $(KCOMPILE)
$(COMPILED_FILE): $(LANGUAGE_FILE) $(TOOL_DIR_FILES) $(MAUDE_FILES) Makefile
	$(KCOMPILE) $(LANGUAGE_FILE) -l $(LANGUAGE_NAME)

# this should build the latex
latex: $(LATEX_FILE)

$(LATEX_FILE):  $(LANGUAGE_FILE) $(TOOL_DIR_FILES) $(MAUDE_FILES) Makefile
	$(KCOMPILE) $(MAIN_FILE) -style $(LATEX_STYLE) -latex $(LANGUAGE_MODULES)

pdf: $(PDF_FILE)
	
$(PDF_FILE): $(LATEX_FILE) 
	pdflatex $(MAIN_FILE)

# to satisfy the target "test", it needs to satisfy the targets "test-a test-b test-c" for a b c \in $(TESTS)
test: $(COMPILED_FILE) $(addprefix test-,$(TESTS))

# this is how to satisfy the target "test-%" for some %.  It requires %.maude to exist.  It then runs it through maude
test-%: %
	echo q | maude $<

# used to force targets to run
force: ;
	
clean:
	rm -f $(MAIN_FILE)-compiled.maude kompile_* $(MAIN_FILE).aux $(MAIN_FILE).log $(MAIN_FILE).pdf $(MAIN_FILE).tex
