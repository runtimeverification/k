TEST_DIRS = algorithms/sort \
	    algorithms/dijkstra \
	    algorithms/primes \
	    algorithms/sudoku/1-direct-definition \
	    algorithms/sudoku/2-with-counters \
	    algorithms/sudoku/3-with-decrement \
	    algorithms/sudoku/4-with-squares \
	    languages/agent \
	    languages/challenge \
	    languages/kernelC \
	    languages/paradigmatic/imp/fully-labeled \
	    languages/paradigmatic/imp/fully-syntactic \
	    languages/paradigmatic/imp/labeled-syntax \
	    languages/paradigmatic/imp/no-syntax \
	    languages/paradigmatic/exp/untyped \
	    languages/paradigmatic/exp/type-inference \
	    languages/paradigmatic/simply-typed \
	    languages/paradigmatic/simply-subtyped \
	    languages/paradigmatic/pcf/untyped \
	    languages/paradigmatic/system-F \
	    languages/educational/imppp \
	    languages/educational/simple/untyped \
	    languages/educational/simple/typed/dynamic \
	    languages/educational/simple/typed/static \
	    languages/educational/skool/typed/dynamic \
	    languages/educational/skool/typed/static \
	    languages/educational/skool/untyped \
	    languages/educational/fun/untyped \
	    languages/esolangs/Thue \
	    languages/esolangs/bf \
	    languages/esolangs/befunge93

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
