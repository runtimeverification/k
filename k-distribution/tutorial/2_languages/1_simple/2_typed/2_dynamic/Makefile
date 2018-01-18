DEF=simple-typed-dynamic
EXT=simple
TESTDIR=../programs/*
RESULTDIR=tests
KOMPILE_FLAGS=--transition strict --backend java
KRUN_FLAGS=--output none

include ../../../../../include/ktest.mak

../programs/threads/threads_05.simple: kompile
	cat tests/threads_05.simple.in 2>/dev/null | $(KRUN) $@ -d $(DEFDIR) --search --bound 5 $(CHECK) tests/threads_05.simple.out

../programs/exceptions/exceptions_07.simple \
../programs/threads/threads_01.simple \
../programs/threads/threads_02.simple \
../programs/threads/threads_04.simple \
../programs/threads/threads_06.simple \
../programs/threads/threads_09.simple \
../programs/diverse/div-nondet.simple: kompile
	cat tests/$(notdir $@).in 2>/dev/null | $(KRUN) $@ -d $(DEFDIR) --search --pattern '<output> ListItem(#ostream(1)) ListItem("off") ListItem(#buffer(S:String)) </output>' $(CHECK) tests/$(notdir $@).out

../programs/diverse/dekker.simple \
../programs/threads/threads_03.simple \
../programs/threads/threads_08.simple: kompile
	true
