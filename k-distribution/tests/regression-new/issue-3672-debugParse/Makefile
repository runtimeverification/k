DEF=test
EXT=test
TESTDIR=.
KAST_FLAGS=--debug-parse
PIPEFAIL=
CHECK=$(CONSIDER_ERRORS) $(REMOVE_PATHS) | diff -

include ../../../include/kframework/ktest.mak

update-results: CHECK=$(CONSIDER_ERRORS) $(REMOVE_PATHS) >
