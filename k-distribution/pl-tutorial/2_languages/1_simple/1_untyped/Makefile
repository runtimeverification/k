MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
DEF=simple-untyped
EXT=simple
TESTDIR=tests/*
KOMPILE_FLAGS=--enable-search --md-selector "k&!noio"
KOMPILE_BACKEND?=llvm
KRUN_FLAGS=--output none

include $(MAKEFILE_PATH)/../../../find-k.mak
include ${K_HOME}/include/kframework/ktest.mak

KOMPILED_NOIO_DIR=$(DEFDIR)/noio/$(notdir $(DEF))-kompiled
KOMPILED_IO_DIR=$(DEFDIR)/io/$(notdir $(DEF))-kompiled

$(KOMPILED_NOIO_DIR):
	mkdir -p $@

$(KOMPILED_IO_DIR):
	mkdir -p $@

kompile_no_io: $(KOMPILED_NOIO_DIR)/timestamp

$(KOMPILED_NOIO_DIR)/timestamp: $(DEF).$(SOURCE_EXT)
	$(KOMPILE) --enable-search --md-selector "k&!io" --backend $(KOMPILE_BACKEND) $(DEBUG) $< -d $(DEFDIR)/noio

kompile_io: $(KOMPILED_IO_DIR)/timestamp

$(KOMPILED_IO_DIR)/timestamp: $(DEF).$(SOURCE_EXT)
	$(KOMPILE) --md-selector "k&!noio" --backend $(KOMPILE_BACKEND) $(DEBUG) $< -d $(DEFDIR)/io

tests/exceptions/exceptions_01.simple \
tests/exceptions/exceptions_02.simple \
tests/exceptions/exceptions_03.simple \
tests/exceptions/exceptions_04.simple \
tests/exceptions/exceptions_05.simple \
tests/exceptions/exceptions_06.simple \
tests/exceptions/exceptions_08.simple \
tests/exceptions/exceptions_09.simple \
tests/exceptions/exceptions_10.simple \
tests/exceptions/exceptions_11.simple \
tests/exceptions/exceptions_12.simple \
tests/exceptions/exceptions_13.simple \
tests/exceptions/exceptions_14.simple \
tests/exceptions/exceptions_15.simple \
tests/threads/threads_04.simple \
tests/threads/threads_07.simple \
tests/threads/threads_10.simple \
tests/threads/threads_11.simple \
tests/threads/threads_12.simple \
tests/diverse/factorial.simple \
tests/diverse/collatz.simple \
tests/diverse/matrix.simple \
tests/diverse/higher-order.simple \
tests/diverse/sortings.simple: kompile_io
	cat $@.in 2>/dev/null | $(KRUN_OR_LEGACY) $@ $(KRUN_FLAGS) $(DEBUG) -d $(DEFDIR)/io $(CHECK) $@.out

tests/threads/threads_05.simple: kompile_no_io
	$(KRUN_OR_LEGACY) -cINPUT="ListItem(0)" $@ -d $(DEFDIR) --search --depth 100 -d $(DEFDIR)/noio $(CHECK) $@.out

tests/threads/threads_01.simple \
tests/threads/threads_02.simple \
tests/threads/threads_04.simple \
tests/threads/threads_06.simple \
tests/threads/threads_09.simple \
tests/exceptions/exceptions_07.simple \
tests/diverse/div-nondet.simple: kompile_no_io
	$(KRUN_OR_LEGACY) --search -cINPUT="$$((cat $@.input 2>/dev/null || echo "0")| sed 's/\([[:digit:]]\+\)/ListItem(\1)/g')" $@ -d $(DEFDIR)/noio $(CHECK) $@.out
