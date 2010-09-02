# KCOMPILE can be set by whoever calls this file
# e.g., `make KCOMPILE=xxxxx`
KCOMPILE ?= ../../../tools/kompile.pl

# this is the name of the main maude module 
LANGUAGE_NAME = BASIC-ASM

# this are all interesting modules (used to latexify)
LANGUAGE_MODULES = BASIC-ASM-SYNTAX BASIC-ASM-SEMANTICS

LATEX_STYLE = bb

#this is the basename of the main file
MAIN_FILE = basic-asm

# this is a space-separated list of basename maude files to run
TESTS = basic-asm.m

TOOL_DIR = $(dir $(KCOMPILE))
include $(TOOL_DIR)make-helper.mk
	
