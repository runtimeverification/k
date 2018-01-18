DEF=imp
EXT=imp
KOMPILE_FLAGS=--backend java --transition "division lookup increment assignment read print"
KRUN_FLAGS=--output none

include ../../../../include/ktest.mak


tests/div.imp: kompile
	cat $@.in 2>/dev/null | $(KRUN) $@ -d $(DEFDIR) --search $(CHECK) $@.out

tests/spawn.imp: kompile
	cat $@.in 2>/dev/null | $(KRUN) $@ -d $(DEFDIR) --search --pattern "<store> Store </store> <output> ListItem(_) ListItem(_) ListItem(#buffer(Out:String)) </output>" $(CHECK) $@.out
