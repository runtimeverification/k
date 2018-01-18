DEF=kool-typed-static
EXT=kool
KOMPILE_FLAGS=--backend java --transition inheritance-cycle
KRUN_FLAGS=--output none
TESTDIR=../programs
RESULTDIR=tests

include ../../../../../include/ktest.mak

../programs/cycle.kool: kompile
	cat tests/cycle.kool.in 2>/dev/null | $(KRUN) $@ -d $(DEFDIR) --search --pattern '<output> ListItem(#ostream(1)) ListItem("off") ListItem(#buffer(S:String)) </output>' $(CHECK) tests/cycle.kool.out

../programs/return-object.kool: kompile
	true
