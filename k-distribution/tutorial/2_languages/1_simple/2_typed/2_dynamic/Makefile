MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
DEF=simple-typed-dynamic
EXT=simple
TESTDIR?=../programs/*
RESULTDIR=tests
KOMPILE_FLAGS=--transition strict
KOMPILE_BACKEND?=java
KRUN_FLAGS=--output none

%/threads/threads_05.simple: kompile
	cat tests/threads_05.simple.in 2>/dev/null | $(KRUN) $@ -d $(DEFDIR) --search --bound 5 $(CHECK) tests/threads_05.simple.out

%/exceptions/exceptions_07.simple \
%/threads/threads_01.simple \
%/threads/threads_02.simple \
%/threads/threads_04.simple \
%/threads/threads_06.simple \
%/threads/threads_09.simple \
%/diverse/div-nondet.simple: kompile
	cat tests/$(notdir $@).in 2>/dev/null | $(KRUN) $@ -d $(DEFDIR) --search --pattern '<output> ListItem(#ostream(1)) ListItem("off") ListItem(#buffer(S:String)) </output>' $(CHECK) tests/$(notdir $@).out

%/diverse/dekker.simple \
%/threads/threads_03.simple \
%/threads/threads_08.simple: kompile
	true

include $(MAKEFILE_PATH)/../../../../../include/ktest.mak
