TEST_DIRS = challenge imp imppp agent \
        simple/untyped simple/typed/dynamic simple/typed/static \
	exp/untyped exp/type-inference fun/untyped \
	Thue bf befunge93

.PHONY: all build test clean

all: build

build:
	@for d in $(TEST_DIRS); do if ! make -C $$d ; then echo FAILURE!; exit 1; fi; done

test: 
	@for d in $(TEST_DIRS); do if ! make -C $$d test ; then echo FAILURE!; exit 1; fi; done

clean: 
	@for d in $(TEST_DIRS); do if ! make -C $$d clean ; then echo FAILURE!; exit 1; fi; done
