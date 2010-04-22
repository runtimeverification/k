KCOMPILE ?= $(realpath ../tools/kcompile.sh)
TEST_DIRS = befunge93 challenge imp imppp simple/untyped simple/typed/dynamic simple/typed/static

.PHONY: all

all:
	@for d in $(TEST_DIRS); do (make -C $$d test KCOMPILE=$(KCOMPILE)); done

	
