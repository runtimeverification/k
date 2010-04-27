KCOMPILE ?= $(realpath ../tools/kcompile.sh)
TEST_DIRS = befunge93 challenge imp \
	imppp simple/untyped simple/typed/dynamic simple/typed/static \
	bf Thue

.PHONY: all build test clean

all: build

build:
	@for d in $(TEST_DIRS); do (make -C $$d KCOMPILE=$(KCOMPILE)); done

test: 
	@for d in $(TEST_DIRS); do (make -C $$d test KCOMPILE=$(KCOMPILE)); done

clean: 
	@for d in $(TEST_DIRS); do (make -C $$d clean KCOMPILE=$(KCOMPILE)); done
