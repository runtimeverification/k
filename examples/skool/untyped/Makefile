# KCOMPILE can be set by whoever calls this file
# e.g., `make KCOMPILE=xxxxx`
KCOMPILE ?= ../../../tools/kompile.pl

# this is the name of the main maude module 
LANGUAGE_NAME = SKOOL-UNTYPED

# this are all interesting modules (used to latexify)
LANGUAGE_MODULES = SKOOL-UNTYPED-SORTS SKOOL-UNTYPED-EXPR SKOOL-UNTYPED-DECL SKOOL-UNTYPED-STMT SKOOL-UNTYPED-STMTS SKOOL-UNTYPED-CONFIG SKOOL-UNTYPED-PREPROCESSING SKOOL-UNTYPED-EXPR-EVALUATION SKOOL-UNTYPED-FUNCTION-CALL SKOOL-UNTYPED-INSTR-PROCESSING

LATEX_STYLE = bb

#this is the basename of the main file
MAIN_FILE = skool-untyped

# this is a space-separated list of basename maude files to run
TESTS = skool-untyped-test.m

TOOL_DIR = $(dir $(KCOMPILE))
include $(TOOL_DIR)make-helper.mk

