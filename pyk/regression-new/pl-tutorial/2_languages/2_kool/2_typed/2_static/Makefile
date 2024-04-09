DEF=kool-typed-static
EXT=kool
KOMPILE_FLAGS=--enable-search
KRUN_FLAGS=--output none
TESTDIR?=../programs
RESULTDIR=tests

%/cycle.kool: kompile
	cat tests/cycle.kool.in 2>/dev/null | $(KRUN) $@ --definition $(DEF)-kompiled --search --pattern '<output> ListItem(#ostream(1)) ListItem("off") ListItem(#buffer(S:String)) </output>' $(CHECK) tests/cycle.kool.out

%/return-object.kool: kompile
	true

include ../../../../../include/ktest.mak
