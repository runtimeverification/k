DEF=imp
EXT=imp
KRUN_FLAGS=--output none
KOMPILE_FLAGS=--gen-glr-bison-parser --enable-search

include ../../../find-k.mak
include ${K_HOME}/include/kframework/ktest.mak


tests/div.imp: kompile
	cat $@.in 2>/dev/null | $(KRUN_OR_LEGACY) $@ --definition $(DEF)-kompiled --search $(CHECK) $@.out

tests/spawn.imp: kompile
	cat $@.in 2>/dev/null | $(KRUN_OR_LEGACY) $@ --definition $(DEF)-kompiled --search --pattern "<store> Store </store> <output> ListItem(_) ListItem(_) ListItem(#buffer(Out:String)) </output>" $(CHECK) $@.out
