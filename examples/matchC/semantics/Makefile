K_ROOT_DIR = $(HOME)/k-framework

LANG_NAME = kernelC
EXT_NAME = matchC

K_TOOLS_DIR = $(K_ROOT_DIR)/tools
ANTLR_ROOT_DIR = $(K_TOOLS_DIR)/antlr
KC = $(K_TOOLS_DIR)/kompile.pl
KFLAGS = -v -c
JVM = java
CLASSPATH = $(ANTLR_ROOT_DIR)/antlrworks-1.4.jar:$(ANTLR_ROOT_DIR)
JFLAGS = -classpath $(CLASSPATH)
UNWRAP_MAIN = unwrapBuiltinsMain

LANG_K_SYNTAX = $(LANG_NAME)-syntax.k
LANG_K_SEMANTICS = $(LANG_NAME)-semantics.k
LANG_K_MAIN = $(LANG_NAME).k
LANG_K_FLAT = $(LANG_NAME)-flat.k
LANG_MAUDE_SYNTAX = $(LANG_NAME)-syntax.maude
LANG_COMPILED_FILE = $(LANG_NAME)-flat-compiled.maude
LANG_UW_FILE = $(LANG_NAME)-uw.maude

EXT_K_SYNTAX = $(EXT_NAME)-syntax.k
EXT_K_SEMANTICS = $(EXT_NAME)-semantics.k
EXT_K_MAIN = $(EXT_NAME).k
EXT_K_FLAT = $(EXT_NAME)-flat.k
EXT_MAUDE_SYNTAX = $(EXT_NAME)-syntax.maude
EXT_COMPILED_FILE = $(EXT_NAME)-flat-compiled.maude
EXT_UW_FILE = $(EXT_NAME)-uw.maude


%-uw.maude: %-flat-compiled.maude
	$(JVM) $(JFLAGS) $(UNWRAP_MAIN) <$< >$@

%-flat-compiled.maude: %-flat.maude
	$(KC) -c -l `echo $* | tr [:lower:] [:upper:]` $<
	@sed -i -e '1d' -e '/^mod/a \
    subsort Formula Subst MathObj++ List{MathObj++} Set{MathObj++} Value TypedValue ExpressionType < Builtins KResult . \
    subsort Id Field < Builtins KProper .' $@

%.maude: %.k
	$(KC) -m $<
	@sed -i -e 's/Int + +/Int++/g' $@

%-flat.k: %.k
	$(KC) -flat $*


all: build

build: $(EXT_UW_FILE) \
       $(LANG_UW_FILE) \
       $(EXT_COMPILED_FILE) \
       $(LANG_COMPILED_FILE) \
       $(EXT_MAUDE_SYNTAX) \
       $(LANG_MAUDE_SYNTAX)


clean:
	rm -f *-flat.k *.maude kompile_* *~

