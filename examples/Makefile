TEST_DIRS = modules/tests/exp modules/tests/lambda modules/tests/mu \
	    modules/tests/io modules/tests/imp modules/tests/halt \
            modules/tests/callcc modules/tests/threads modules/tests/agents \
	    modules/tests/quote-unquote \
	    algorithms/sort algorithms/dijkstra \
            agent lambda/simply-typed \
        challenge imp/fully-labeled imp/fully-syntactic imp/labeled-syntax imppp \
        simple/untyped simple/typed/dynamic simple/typed/static \
        skool/typed/dynamic \
	kernelc \
	exp/untyped exp/type-inference fun/untyped \
	Thue bf befunge93

.PHONY: all build test clean

all: build

build:
	@for d in $(TEST_DIRS); do echo Making $$d ; if ! make -C $$d ; then echo FAILURE! in $$d; exit 1; fi; done

test: 
	@for d in $(TEST_DIRS); do  echo Testing $$d ; if ! make -C $$d test ; then echo FAILURE! in $$d; exit 1; fi; done

pdf: 
	@for d in $(TEST_DIRS); do  echo Typesetting $$d ; if ! make -C $$d pdf ; then echo FAILURE! in $$d; exit 1; fi; done

clean: 
	@for d in $(TEST_DIRS); do if ! make -C $$d clean ; then echo FAILURE!; exit 1; fi; done
