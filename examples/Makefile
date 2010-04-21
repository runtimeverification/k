KCOMPILE ?= $(realpath ../tools/kcompile.sh)
TEST_DIRS = befunge93 challenge

.PHONY: all

all:
	@for d in $(TEST_DIRS); do (make -C $$d test KCOMPILE=$(KCOMPILE)); done

	