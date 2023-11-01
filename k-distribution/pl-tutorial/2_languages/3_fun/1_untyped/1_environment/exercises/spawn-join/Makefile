MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
TESTDIR=tests
include $(MAKEFILE_PATH)/../../Makefile

tests/ex-%.fun: KRUN_FLAGS=--search --pattern '<output>... ListItem(\#buffer(S:String)) </output>'

tests/references-5.fun: kompile
	true
