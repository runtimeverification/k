K_ROOTDIR = ~/k-framework
ML_ROOTDIR = $(K_ROOTDIR)/examples/ml-imp2.0

.SUFFIXES: .imp .maude
LANG_NAME = imp

K_TOOLSDIR = $(K_ROOTDIR)/tools
KC = $(K_TOOLSDIR)/kompile.pl
ANTLR_ROOTDIR = $(K_TOOLSDIR)/antlr
ANTLR_MAKEFILE = Makefile.antlr
MLC = $(ML_ROOTDIR)/mlc.sh
TARGET = run
UNWRAP = unwrapBuiltinsMain
MAUDE = maude

K_SYNTAX = $(LANG_NAME)-syntax.k
K_SEMANTICS = $(LANG_NAME)-semantics.k
K_MAIN = $(LANG_NAME).k
MAUDE_SYNTAX = $(LANG_NAME)-syntax.maude
MAUDE_SEMANTICS = $(LANG_NAME)-semantics.maude
MAUDE_MAIN = $(LANG_NAME).maude
COMPILED_FILE = $(LANG_NAME)-compiled.maude
ML_MAIN = ml-$(LANG_NAME).maude
TEST_FILE = ml-test

.PHONY: run

# compile a .imp file into a .maude file
.imp.maude: 
	$(MLC) $<
	$(MAKE) -C $(ANTLR_ROOTDIR) -f $(ANTLR_MAKEFILE) $(TARGET) MAIN=$(UNWRAP) <$(PWD)/$@ >$(PWD)/.tmp.maude
	mv .tmp.maude $@ 
	sed -i -e '/^load/d' -e '/^make/d' $@
	sed -i -e "1i\load $(ML_ROOTDIR)/fol.maude" -e "1i\load $(ML_ROOTDIR)/ml-imp.maude" -e "s/including IMP/\0 + FOL=/" $@
	echo "rew check('prog-`basename $@ .maude`) ." >> $@

all: configure build

run: build
	$(MAUDE) $(TEST_FILE)

build: $(ML_MAIN)

maudify: $(MAUDE_MAIN)

configure:
	$(MAKE) -C $(ANTLR_ROOTDIR) -f $(ANTLR_MAKEFILE)

$(ML_MAIN): $(COMPILED_FILE)
	$(MAKE) -C $(ANTLR_ROOTDIR) -f $(ANTLR_MAKEFILE) $(TARGET) MAIN=$(UNWRAP) <$(PWD)/$(COMPILED_FILE) >$(PWD)/$(ML_MAIN)
	@sed -i '/^make/d' $(ML_MAIN)
	@sed -i '/^java/d' $(ML_MAIN)
	@sed -i '/^mod IMP is/a \
    subsort Formula Subst MathObj++ List{MathObj++} Set{MathObj++} Value TypedValue ExpressionType < Builtins KResult . \
    subsort Id Field < Builtins KProper .' $(ML_MAIN)

$(COMPILED_FILE): $(MAUDE_MAIN) $(MAUDE_SYNTAX) $(MAUDE_SEMANTICS)
	$(KC) -c $(LANG_NAME)

$(MAUDE_MAIN) $(MAUDE_SYNTAX) $(MAUDE_SEMANTICS): $(K_MAIN) $(K_SYNTAX) $(K_SEMANTICS)
	$(KC) -m $(LANG_NAME)
	@sed -i 's/\: : Int/: : IntSort/g' $(MAUDE_MAIN)
	@sed -i 's/\: : Int/: : IntSort/g' $(MAUDE_SYNTAX)
	@sed -i 's/\: : Int/: : IntSort/g' $(MAUDE_SEMANTICS)
	@sed -i 's/Int + +/Int++/g' $(MAUDE_MAIN)
	@sed -i 's/Int + +/Int++/g' $(MAUDE_SYNTAX)
	@sed -i 's/Int + +/Int++/g' $(MAUDE_SEMANTICS)

clean:
	rm -f $(MAUDE_SYNTAX) $(MAUDE_SEMANTICS) $(MAUDE_MAIN) $(COMPILED_FILE) $(ML_MAIN) kcompile_*

