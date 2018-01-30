MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
TESTDIR=tests
include $(MAKEFILE_PATH)/../../Makefile

tests/ex-%.fun: KRUN_FLAGS+=--output none

tests/ex-12.fun: kompile
	cat tests/ex-12.fun.in 2>/dev/null | $(KRUN) $@ -d $(DEFDIR) --search --pattern "<output>... ListItem(#buffer(S:String)) </output>" $(CHECK) tests/ex-12.fun.out

tests/references-5.fun: kompile
	true
