MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
DEF=simple-typed-static
EXT=simple
TESTDIR?=../programs/*
RESULTDIR=tests
KOMPILE_BACKEND?=java
KRUN_FLAGS=--pattern "<tasks> .Bag </tasks>" --smt none

include $(MAKEFILE_PATH)/../../../../find-k.mak
include ${K_HOME}/include/ktest.mak
