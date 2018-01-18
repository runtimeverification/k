include ../../2_imp/lesson_1/Makefile
KOMPILE_FLAGS+=--transition division --backend java

tests/div.imp: kompile
	cat $@.in 2>/dev/null | $(KRUN) $@ -d $(DEFDIR) --search $(CHECK) $@.out
