MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
TESTDIR=tests
include $(MAKEFILE_PATH)/../../Makefile

KOMPILE_FLAGS=--transition "lookup assignment io"
KOMPILE_BACKEND?=java

tests/ex-%.fun: KRUN_FLAGS=--search --pattern '<output>... ListItem(\#buffer(S:String)) </output>'

tests/references-5.fun: kompile
	true
