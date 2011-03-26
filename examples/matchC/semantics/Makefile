K_ROOT_DIR = $(HOME)/k-framework
ML_ROOT_DIR = ..

LANG_NAME = kernelC
EXT_NAME = matchC

K_TOOLS_DIR = $(K_ROOT_DIR)/tools
KC = $(K_TOOLS_DIR)/kompile.pl
ML_LIB_DIR = $(ML_ROOT_DIR)/lib
ML_PRELUDE = $(ML_LIB_DIR)/ml-prelude.maude
#ML_PRELUDE_STRING = `echo $(ML_PRELUDE) | sed 's/\//\\\//g'`
ML_PRELUDE_STRING = ..\/lib\/ml-prelude.maude

LANG_K_SYNTAX = $(LANG_NAME)-syntax.k
LANG_K_SEMANTICS = $(LANG_NAME)-semantics.k
LANG_K_MAIN = $(LANG_NAME).k
LANG_MAUDE_SYNTAX = $(LANG_K_SYNTAX:.k=.maude)
LANG_MAUDE_MAIN = $(LANG_K_MAIN:.k=.maude)
LANG_COMPILED_FILE = $(LANG_NAME)-compiled.maude
LANG_K_FILES = $(LANG_K_SYNTAX) $(LANG_K_SEMANTICS) $(LANG_K_MAIN)
LANG_MAUDE_FILES = $(LANG_K_FILES:.k=.maude)

EXT_K_SYNTAX = $(EXT_NAME)-syntax.k
EXT_K_SEMANTICS = $(EXT_NAME)-semantics.k
EXT_K_MAIN = $(EXT_NAME).k
EXT_MAUDE_SYNTAX = $(EXT_K_SYNTAX:.k=.maude)
EXT_MAUDE_MAIN = $(EXT_K_MAIN:.k=.maude)
EXT_COMPILED_FILE = $(EXT_NAME)-compiled.maude
EXT_K_FILES = $(LANG_K_SYNTAX) $(LANG_K_SEMANTICS) \
              $(EXT_K_SYNTAX) $(EXT_K_SEMANTICS) $(EXT_K_MAIN)
EXT_MAUDE_FILES = $(EXT_K_FILES:.k=.maude)

CLEAN_FILES = $(LANG_COMPILED_FILE) \
              $(LANG_MAUDE_FILES) \
              $(EXT_COMPILED_FILE) \
              $(EXT_MAUDE_FILES) \
              shared.maude


%-compiled.maude: %.maude
	$(KC) -c $<
	@sed -i -e '1s/^.*k-prelude/load $(ML_PRELUDE_STRING)/' $@


all: build

build: $(EXT_COMPILED_FILE) \
       $(EXT_MAUDE_SYNTAX)


$(EXT_MAUDE_MAIN) $(EXT_MAUDE_SYNTAX): $(EXT_K_FILES)
	$(KC) -m -prelude $(ML_PRELUDE) $(EXT_K_MAIN)

$(LANG_MAUDE_MAIN) $(LANG_MAUDE_SYNTAX): $(LANG_K_FILES)
	$(KC) -m -shared $(ML_PRELUDE) $(LANG_K_MAIN)


clean:
	rm -f $(CLEAN_FILES) kompile_* *~

