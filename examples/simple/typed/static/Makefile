# KCOMPILE can be set by whoever calls this file
# e.g., `make KCOMPILE=xxxxx`
KCOMPILE ?= ../../../../tools/kompile.pl

# this is the name of the main maude module 
LANGUAGE_NAME = SIMPLE-TYPED-STATIC

# this are all interesting modules (used to latexify)
LANGUAGE_MODULES = SIMPLE-TYPED-SORTS SIMPLE-TYPED-EXPR SIMPLE-TYPED-DECL SIMPLE-TYPED-STMT SIMPLE-TYPED-STMTS SIMPLE-TYPED-STATIC-CONFIG SIMPLE-TYPED-STATIC-PREPROCESSING SIMPLE-TYPED-STATIC-EXPR-EVALUATION SIMPLE-TYPED-STATIC-FUNCTIONS-PROCESSING SIMPLE-TYPED-STATIC-SEMANTICS

LATEX_STYLE = bb

#this is the basename of the main file
MAIN_FILE = simple-typed-static

# this is a space-separated list of basename maude files to run
TESTS = simple-typed-static-test.maude

TOOL_DIR = $(dir $(KCOMPILE))
include $(TOOL_DIR)make-helper.mk
	
