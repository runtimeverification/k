MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
DEF=imp
EXT=imp
TESTDIR=.
KOMPILE_BACKEND=llvm
export KOMPILE_BACKEND
KRUN_FLAGS=--parser "cat"

include ../include/ktest.mak
