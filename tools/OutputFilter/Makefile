all:
	ghc --make Main -o filterOutput -O2 -H14m

static:
	ghc --make -static -optl-static -optl-pthread Main -o filterOutput -O2 -H14m

clean:
	rm -f *.hi
	rm -f *.o
	rm -f filterOutput
	rm -f Data/Yaml/*.hi
	rm -f Data/Yaml/*.o
