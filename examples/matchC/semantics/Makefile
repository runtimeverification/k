ML_ROOT_DIR = ..
K_ROOT_DIR = $(ML_ROOT_DIR)/../..

LANG_NAME = kernelC
EXT_NAME = matchC

K_TOOLS_DIR = $(K_ROOT_DIR)/tools
KC = $(K_TOOLS_DIR)/kompile.pl
ML_LIB_DIR = $(ML_ROOT_DIR)/lib
ML_PATTERNS_DIR = $(ML_ROOT_DIR)/patterns
ML_PRELUDE = $(ML_LIB_DIR)/ml-prelude.maude

LANG_K_SYNTAX = $(LANG_NAME)-syntax.k
LANG_K_SEMANTICS = $(LANG_NAME)-semantics.k
LANG_K_MAIN = $(LANG_NAME).k
LANG_MAUDE_MAIN = $(LANG_K_MAIN:.k=.maude)
LANG_COMPILED_FILE = $(LANG_NAME)-compiled.maude
LANG_K_FILES = $(LANG_K_SYNTAX) $(LANG_K_SEMANTICS) $(LANG_K_MAIN)
LANG_MAUDE_FILES = $(LANG_K_FILES:.k=.maude)

EXT_K_SYNTAX = $(EXT_NAME)-syntax.k
EXT_K_SEMANTICS = $(EXT_NAME)-semantics.k
EXT_K_MAIN = $(EXT_NAME).k
EXT_K_FOL = $(ML_LIB_DIR)/fol.k
EXT_K_IO = $(ML_PATTERNS_DIR)/io.k
EXT_K_LIST = $(ML_PATTERNS_DIR)/list.k
EXT_K_STACK = $(ML_PATTERNS_DIR)/stack.k
EXT_K_BINARY_TREE = $(ML_PATTERNS_DIR)/binary_tree.k
EXT_MAUDE_MAIN = $(EXT_K_MAIN:.k=.maude)
EXT_COMPILED_FILE = $(EXT_NAME)-compiled.maude
EXT_K_FILES = $(LANG_K_SYNTAX) $(LANG_K_SEMANTICS) \
              $(EXT_K_SYNTAX) $(EXT_K_SEMANTICS) \
              $(EXT_K_FOL) \
              $(EXT_K_IO) $(EXT_K_LIST) $(EXT_K_STACK) $(EXT_K_BINARY_TREE) \
              $(EXT_K_MAIN)
EXT_MAUDE_FILES = $(EXT_K_FILES:.k=.maude)

CLEAN_FILES = $(LANG_COMPILED_FILE) \
              $(LANG_COMPILED_FILE)-e \
              $(LANG_MAUDE_FILES) \
              $(EXT_COMPILED_FILE) \
              $(EXT_COMPILED_FILE)-e \
              $(EXT_MAUDE_FILES) \
              shared.maude


%-compiled.maude: %.maude
	$(KC) -c -prelude $(ML_PRELUDE) $<


all: build

build: $(EXT_COMPILED_FILE)


$(EXT_MAUDE_MAIN): $(EXT_K_FILES)
	$(KC) -m -prelude $(ML_PRELUDE) $(EXT_K_MAIN)

$(LANG_MAUDE_MAIN): $(LANG_K_FILES)
	$(KC) -m -prelude $(ML_PRELUDE) $(LANG_K_MAIN)


clean:
	rm -f $(CLEAN_FILES) kompile_* *~

