K_ROOT_DIR = $(HOME)/k-framework

LANG_NAME = kernelC
EXT_NAME = matchC

K_TOOLS_DIR = $(K_ROOT_DIR)/tools
ANTLR_ROOT_DIR = $(K_TOOLS_DIR)/antlr
KC = $(K_TOOLS_DIR)/kompile.pl
JVM = java
CLASSPATH = $(ANTLR_ROOT_DIR)/antlrworks-1.4.jar:$(ANTLR_ROOT_DIR)
JFLAGS = -classpath $(CLASSPATH)
UNWRAP_MAIN = unwrapBuiltinsMain


LANG_K_SYNTAX = $(LANG_NAME)-syntax.k
LANG_K_SEMANTICS = $(LANG_NAME)-semantics.k
LANG_K_MAIN = $(LANG_NAME).k
LANG_MAUDE_SYNTAX = $(LANG_K_SYNTAX:.k=.maude)
LANG_MAUDE_MAIN = $(LANG_K_MAIN:.k=.maude)
LANG_COMPILED_FILE = $(LANG_NAME)-compiled.maude
LANG_UW_FILE = $(LANG_NAME)-uw.maude
LANG_K_FILES = $(LANG_K_SYNTAX) $(LANG_K_SEMANTICS) $(LANG_K_MAIN)
LANG_MAUDE_FILES = $(LANG_K_FILES:.k=.maude)


EXT_K_SYNTAX = $(EXT_NAME)-syntax.k
EXT_K_SEMANTICS = $(EXT_NAME)-semantics.k
EXT_K_MAIN = $(EXT_NAME).k
EXT_MAUDE_SYNTAX = $(EXT_K_SYNTAX:.k=.maude)
EXT_MAUDE_MAIN = $(EXT_K_MAIN:.k=.maude)
EXT_COMPILED_FILE = $(EXT_NAME)-compiled.maude
EXT_UW_FILE = $(EXT_NAME)-uw.maude
EXT_K_FILES = $(LANG_K_FILES) $(EXT_K_SYNTAX) $(EXT_K_SEMANTICS) $(EXT_K_MAIN)
EXT_MAUDE_FILES = $(EXT_K_FILES:.k=.maude)


CLEAN_FILES = $(LANG_UW_FILE) \
              $(LANG_COMPILED_FILE) \
              $(LANG_MAUDE_FILES) \
              $(EXT_UW_FILE) \
              $(EXT_COMPILED_FILE) \
              $(EXT_MAUDE_FILES)


%-uw.maude: %-compiled.maude
	$(JVM) $(JFLAGS) $(UNWRAP_MAIN) <$< >$@

%-compiled.maude: %.maude
	$(KC) -c -l `echo $* | tr [:lower:] [:upper:]` $<
	@sed -i -e '1d' -e '/^mod/a \
    subsort Formula Subst MathObj++ List{MathObj++} Set{MathObj++} Value TypedValue ExpressionType < Builtins KResult . \
    subsort Id Field < Builtins KProper .' $@

%.maude: %.k
	$(KC) -m $<
	@sed -i -e 's/Int + +/Int++/g' $@


$(EXT_MAUDE_MAIN): $(EXT_K_FILES)
	$(KC) -m $(EXT_K_MAIN)
	sed -i -e 's/Int + +/Int++/g' $(EXT_MAUDE_FILES)

$(LANG_MAUDE_MAIN): $(LANG_K_FILES)
	$(KC) -m $(LANG_K_MAIN)
	sed -i -e 's/Int + +/Int++/g' $(LANG_MAUDE_FILES)



all: build

build: $(EXT_UW_FILE) \
       $(LANG_UW_FILE) \
       $(EXT_COMPILED_FILE) \
       $(LANG_COMPILED_FILE) \
       $(EXT_MAUDE_SYNTAX) \
       $(LANG_MAUDE_SYNTAX)


clean:
	rm -f $(CLEAN_FILES) kompile_* *~

