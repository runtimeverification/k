

COMPILER=../../../K2Java/bin/k3ompile.jar

COMPILE=java -jar $(COMPILER) -c
FILE=ocl.k
TEST=programs/test-if.ocl

all:
	$(COMPILE) $(FILE)

test:
	krun $(TEST) --parser="java -jar $(COMPILER) -kast"
#	krun $(TEST)

kast:
	java -jar $(COMPILER) -kast $(TEST)

clean:
	rm -rf .k *-compiled.maude
