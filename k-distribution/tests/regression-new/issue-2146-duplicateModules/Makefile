DEF=test
EXT=test
TESTDIR=.
KOMPILE_FLAGS=--syntax-module TEST

%.k %.md: dummy
	$(KOMPILE) $(KOMPILE_FLAGS) --backend $(KOMPILE_BACKEND) $(DEBUG_FAIL) $@ -d $(DEFDIR) 2>&1 | sed '0,/Source/ s!Source[^\n]*!Source...!' | sed 's!'`pwd`'/\(\./\)\{0,2\}!!g' $(CHECK) $@.out $(CHECK2)

include ../../../include/kframework/ktest-fail.mak
