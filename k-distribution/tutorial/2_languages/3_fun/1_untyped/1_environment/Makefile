MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
DEF=fun-untyped
EXT=fun
TESTDIR?=../../programs
RESULTDIR=tests
KOMPILE_FLAGS?=--transition strict
KOMPILE_BACKEND?=java
KRUN_FLAGS?=--pattern "<k> V:K </k>"

%/references-5.fun: kompile
	cat tests/references-5.fun.in 2>/dev/null | $(KRUN) $@ -d $(DEFDIR) --search --pattern "<k> V:K </k>" $(CHECK) tests/references-5.fun.out

include $(MAKEFILE_PATH)/../../../../../include/ktest.mak
