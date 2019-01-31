MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
DEF=fun-untyped
EXT=fun
TESTDIR?=../../programs
RESULTDIR=tests
KOMPILE_BACKEND?=java
KRUN_FLAGS=--pattern "<k> V:K </k>"

%/calcc-looping.fun \
%/references-5.fun \
%/constructor-bst-sorting.fun \
%/constructor-expr-distributivity.fun \
%/factorial-and-list-max.fun \
%/nth.fun \
%/pattern.fun \
%/references-1.fun \
%/stuck-letrec.fun: kompile
	true

include $(MAKEFILE_PATH)/../../../../../include/ktest.mak
