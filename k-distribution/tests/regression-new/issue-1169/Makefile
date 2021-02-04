DEF=test
DEF2=test2
EXT=test
TESTDIR=.

include ../../../include/kframework/ktest.mak

$(KOMPILED_DIR)/timestamp: $(DEF).k
	$(KOMPILE) $(DEF).k -E > $(DEF2).k
	$(KOMPILE) $(DEF2).k --no-prelude --main-module TEST --syntax-module TEST
	rm -rf $(KOMPILED_DIR)
	mv test2-kompiled $(KOMPILED_DIR)

clean:
	rm -rf test2-kompiled test-kompiled
