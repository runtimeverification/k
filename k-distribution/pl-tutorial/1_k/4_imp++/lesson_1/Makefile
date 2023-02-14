MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
include $(MAKEFILE_PATH)/../../2_imp/lesson_1/Makefile
KOMPILE_FLAGS+=--enable-search

tests/div.imp: kompile
	cat $@.in 2>/dev/null | $(KRUN_OR_LEGACY) $@ -d $(DEFDIR) --search $(CHECK) $@.out
