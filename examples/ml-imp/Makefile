K_ROOTDIR = ~/k-framework
ML_ROOTDIR = $(K_ROOTDIR)/examples/ml-imp

.SUFFIXES: .imp .maude
LANG_NAME = imp

K_TOOLSDIR = $(K_ROOTDIR)/tools
KC = $(K_TOOLSDIR)/kompile.pl
ANTLR_ROOTDIR = $(K_TOOLSDIR)/antlr
ANTLR_MAKEFILE = Makefile.antlr
MLC = $(ML_ROOTDIR)/mlc.sh
TARGET = run
MAIN_CLASS = unwrapBuiltinsMain
MAUDE = maude

K_SYNTAX_FILE = $(LANG_NAME)-syntax.k
K_SEMANTICS_FILE = $(LANG_NAME)-semantics.k
K_MAIN_FILE = $(LANG_NAME).k
MAUDE_SYNTAX_FILE = $(LANG_NAME)-syntax.maude
MAUDE_SEMANTICS_FILE = $(LANG_NAME)-semantics.maude
MAUDE_MAIN_FILE = $(LANG_NAME).maude
COMPILED_FILE = $(LANG_NAME)-compiled.maude
ML_FILE = ml-$(LANG_NAME).maude
TEST_FILE = ml-test

.PHONY: run

# compile a .imp file into a .maude file
.imp.maude: 
	$(MLC) $<
	$(MAKE) -C $(ANTLR_ROOTDIR) -f $(ANTLR_MAKEFILE) $(TARGET) MAIN=$(MAIN_CLASS) <$(PWD)/$@ >$(PWD)/.tmp.maude
	mv .tmp.maude $@ 
	sed -i -e '/^load/d' -e '/^make/d' $@
	sed -i -e "1i\load $(ML_ROOTDIR)/fol.maude" -e "1i\load $(ML_ROOTDIR)/ml-imp.maude" -e "s/including IMP/\0 + FOL=/" $@
	echo "rew check('prog-`basename $@ .maude`) ." >> $@

all: build

run: build
	$(MAUDE) $(TEST_FILE)

build: $(ML_FILE)

maudify: $(MAUDE_MAIN_FILE)

configure:
	$(MAKE) -C $(ANTLR_ROOTDIR) -f $(ANTLR_MAKEFILE)
	sed 's/PL-BUILTINS/BASIC-PL-BUILTINS/' $(K_ROOTDIR)/pl-builtins.maude >pl-builtins.maude
	cp $(K_ROOTDIR)/k-prelude.maude .

$(ML_FILE): $(COMPILED_FILE)
	$(MAKE) -C $(ANTLR_ROOTDIR) -f $(ANTLR_MAKEFILE) $(TARGET) MAIN=$(MAIN_CLASS) <$(PWD)/$(COMPILED_FILE) >$(PWD)/$(ML_FILE)
	sed -i '/^make/d' $(ML_FILE)

$(COMPILED_FILE): $(MAUDE_MAIN_FILE) $(MAUDE_SYNTAX_FILE) $(MAUDE_SEMANTICS_FILE)
	$(KC) -c $(LANG_NAME)
	sed -i '/^load/d' $(COMPILED_FILE)

$(MAUDE_MAIN_FILE): $(K_MAIN_FILE) $(K_SYNTAX_FILE) $(K_SEMANTICS_FILE)
	$(KC) -m $(LANG_NAME)
	sed -i 's/\: : Int/: : IntSort/g' $(MAUDE_SYNTAX_FILE)
	sed -i 's/\: : Int/: : IntSort/g' $(MAUDE_SEMANTICS_FILE)

clean:
	rm -f $(MAUDE_SYNTAX_FILE) $(MAUDE_SEMANTICS_FILE) $(MAUDE_MAIN_FILE) $(COMPILED_FILE) $(ML_FILE) kcompile_*

