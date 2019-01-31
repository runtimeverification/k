MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
DEF=imp
EXT=imp
KOMPILE_FLAGS=--transition "division lookup increment assignment read print"
KOMPILE_BACKEND?=java
KRUN_FLAGS=--output none

include $(MAKEFILE_PATH)/../../../../include/ktest.mak


tests/div.imp: kompile
	cat $@.in 2>/dev/null | $(KRUN) $@ -d $(DEFDIR) --search $(CHECK) $@.out

tests/spawn.imp: kompile
	cat $@.in 2>/dev/null | $(KRUN) $@ -d $(DEFDIR) --search --pattern "<output> ListItem(_) ListItem(_) ListItem(#buffer(Out:String)) </output>" $(CHECK) $@.out
