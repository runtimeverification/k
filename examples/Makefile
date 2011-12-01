TEST_DIRS = algorithms/sort \
	    algorithms/dijkstra \
	    algorithms/primes \
	    algorithms/sudoku/1-direct-definition \
	    algorithms/sudoku/2-with-counters \
	    algorithms/sudoku/3-with-decrement \
	    algorithms/sudoku/4-with-squares \
	    languages/classic/exp/untyped/environment \
	    languages/classic/exp/untyped/substitution \
	    languages/classic/lambda/simply-typed \
	    languages/classic/pcf/untyped/ \
	    languages/classic/lambda/polymorphism/system-F \
	    languages/research/imppp \
	    languages/research/simple/untyped \
	    languages/research/simple/typed/dynamic \
	    languages/research/simple/typed/static \
	    languages/research/kool/untyped \
	    languages/research/fun/untyped \
	    languages/research/agent \
	    languages/research/challenge \
	    languages/classic/imp \
#	    languages/classic/exp/type-inference \
#	    languages/research/kernelC \
		#languages/research/kool/typed/static \
		#languages/research/kool/typed/dynamic \
	    #languages/classic/imp/fully-syntactic \
	    #languages/classic/imp/labeled-syntax \
	    #languages/classic/imp/no-syntax 

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
