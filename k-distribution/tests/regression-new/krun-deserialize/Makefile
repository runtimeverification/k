MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
DEF=imp
EXT=imp
TESTDIR=.
KOMPILE_BACKEND=llvm
export KOMPILE_BACKEND
KRUN_FLAGS=--parser "cat"

include ../../../include/kframework/ktest.mak

# Use krun for these tests instead of kx.
# Setting KOMPILE_BACKEND=llvm above uses the value of KX to run tests, so
# setting it equal to KRUN causes the actual krun to be used in any case.
KRUN_OR_KX=$(KRUN)
