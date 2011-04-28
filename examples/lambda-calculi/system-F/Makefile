# KCOMPILE can be set by whoever calls this file
# e.g., `make KCOMPILE=xxxxx`
KCOMPILE ?= ../../../tools/kompile.pl

# this is the name of the main maude module 
LANGUAGE_NAME = SYSTEM-F

# this are all interesting modules (used to latexify)
LANGUAGE_MODULES = SYSTEM-F-SYNTAX SYSTEM-F-STATIC-SEMANTICS SYSTEM-F-PROGRAMS SYSTEM-F

LATEX_STYLE = bb
LATEX_TOPMATTER = topmatter.tex

#this is the basename of the main file
MAIN_FILE = system-F

# this is a space-separated list of basename maude files to run
TESTS =

TOOL_DIR = $(dir $(KCOMPILE))
include $(TOOL_DIR)make-helper.mk
