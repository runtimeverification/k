KCOMPILE ?= $(realpath ../tools/kompile.sh)
TEST_DIRS = challenge imp imppp \
        simple/untyped simple/typed/dynamic simple/typed/static \
	exp/untyped exp/type-inference fun/untyped \
	fun/untyped

.PHONY: all build test clean

all: build

build:
	@for d in $(TEST_DIRS); do if ! make -C $$d KCOMPILE=$(KCOMPILE); then echo FAILURE!; exit 1; fi; done

test: 
	@for d in $(TEST_DIRS); do if ! make -C $$d test KCOMPILE=$(KCOMPILE); then echo FAILURE!; exit 1; fi; done

clean: 
	@for d in $(TEST_DIRS); do if ! make -C $$d clean KCOMPILE=$(KCOMPILE); then echo FAILURE!; exit 1; fi; done
