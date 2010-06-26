LANG_NAME = imp

K_ROOTDIR = ~/k-framework
K_TOOLSDIR = $(K_ROOTDIR)/tools
KC = $(K_TOOLSDIR)/kompile.pl
ANTLR_ROOTDIR = $(K_TOOLSDIR)/antlr
#MAKEFILE = $(ANTLR_ROOTDIR)/Makefile.antlr
MAKEFILE = Makefile.antlr
TARGET = run
MAIN_CLASS = unwrapBuiltinsMain
MAUDE = smt-maude

K_SYNTAX_FILE = $(LANG_NAME)-syntax.kmaude
K_SEMANTICS_FILE = $(LANG_NAME)-semantics.kmaude
K_MAIN_FILE = $(LANG_NAME).kmaude
MAUDE_SYNTAX_FILE = $(LANG_NAME)-syntax.maude
MAUDE_SEMANTICS_FILE = $(LANG_NAME)-semantics.maude
MAUDE_MAIN_FILE = $(LANG_NAME).maude
COMPILED_FILE = $(LANG_NAME)-compiled.maude
ML_FILE = ml-$(LANG_NAME).maude
TEST_FILE = ml-test

.PHONY: run

all: build

run: build
	$(MAUDE) $(TEST_FILE)

build: $(ML_FILE)

$(ML_FILE): $(COMPILED_FILE)
	$(MAKE) -C $(ANTLR_ROOTDIR) -f $(MAKEFILE)
	$(MAKE) -C $(ANTLR_ROOTDIR) -f $(MAKEFILE) $(TARGET) MAIN=$(MAIN_CLASS) <$(PWD)/$(COMPILED_FILE) >$(PWD)/$(ML_FILE)
	cat $(ML_FILE) | grep -v "^make" | grep -v "^load" | sed  "12a\subsort Id < KProper ." >$(ML_FILE)

$(COMPILED_FILE): $(MAUDE_MAIN_FILE) $(MAUDE_SYNTAX_FILE) $(MAUDE_SEMANTICS_FILE)
	$(KC) -c $(LANG_NAME)

$(MAUDE_MAIN_FILE): $(K_MAIN_FILE) $(K_SYNTAX_FILE) $(K_SEMANTICS_FILE)
	$(KC) -m $(LANG_NAME)
	sed -i "s/\: : Int/: : IntSort/g" $(MAUDE_SYNTAX_FILE)
	sed -i "s/\: : Int/: : IntSort/g" $(MAUDE_SEMANTICS_FILE)

clean:
	rm -f $(MAUDE_SYNTAX_FILE) $(MAUDE_SEMANTICS_FILE) $(MAUDE_MAIN_FILE) $(COMPILED_FILE) $(ML_FILE) kcompile_*
