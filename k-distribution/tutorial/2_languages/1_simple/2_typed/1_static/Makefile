MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
DEF=simple-typed-static
EXT=simple
TESTDIR?=../programs/*
RESULTDIR=tests
KOMPILE_BACKEND?=java
KRUN_FLAGS=--pattern "<tasks> .Bag </tasks>"

include $(MAKEFILE_PATH)/../../../../../include/ktest.mak
