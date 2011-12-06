TEST_DIRS = \
	    algorithms/dijkstra \
	    algorithms/primes \
	    algorithms/sort \
	    algorithms/sudoku/1-direct-definition \
	    algorithms/sudoku/2-with-counters \
	    algorithms/sudoku/3-with-decrement \
	    algorithms/sudoku/4-with-squares \
	    languages/classic/exp/untyped/environment \
	    languages/classic/exp/untyped/substitution \
	    languages/classic/exp/type-inference \
	    languages/classic/imp \
	    languages/classic/lambda/untyped \
	    languages/classic/lambda/polymorphism/simply-subtyped \
	    languages/classic/lambda/polymorphism/system-F \
	    languages/classic/lambda/simply-typed \
	    languages/classic/pcf/untyped \
	    languages/research/agent \
	    languages/research/challenge \
	    languages/research/fun/untyped \
	    languages/research/imppp \
	    languages/research/kool/typed/static \
	    languages/research/kool/typed/dynamic \
	    languages/research/kool/untyped \
	    languages/research/lambdapp \
	    languages/research/simple/untyped \
	    languages/research/simple/typed/dynamic \
	    languages/research/simple/typed/static \


.PHONY: all build test clean

all: build

build:
	@for d in $(TEST_DIRS); do echo Making $$d ; if ! make -C $$d ; then echo FAILURE! in $$d; exit 1; fi; done

test: 
	@for d in $(TEST_DIRS); do  echo Testing $$d ; if ! make -C $$d test ; then echo FAILURE! in $$d; exit 1; fi; done
	
test-krun: 
	@for d in $(TEST_DIRS); do  echo Testing $$d ; if ! make -C $$d krun-test ; then echo FAILURE! in $$d; exit 1; fi; done

pdf: 
	@for d in $(TEST_DIRS); do  echo Typesetting $$d ; if ! make -C $$d pdf ; then echo FAILURE! in $$d; exit 1; fi; done

clean: 
	@for d in $(TEST_DIRS); do if ! make -C $$d clean ; then echo FAILURE!; exit 1; fi; done
