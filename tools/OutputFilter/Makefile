all:
	ghc --make Main -o filterOutput -O2 -H14m

static:
	ghc --make -static -optl-static -optl-pthread Main -o filterOutput -O2 -H14m

prof:
	ghc --make Main -o filterOutput -O2 -H14m -prof -auto-all

threadscope:
	ghc --make Main -o filterOutput -O2 -H14m -threaded -eventlog

clean:
	rm -f *.hi
	rm -f *.o
	rm -f filterOutput
	rm -f Data/Yaml/*.hi
	rm -f Data/Yaml/*.o
	rm -f *.eventlog
	rm -f *.prof