all: clean
	javac src/*.java;
	javac tests/*.java -cp lib/junit-4.10.jar:src;
	java -cp lib/junit-4.10.jar:src:tests org.junit.runner.JUnitCore AllTests

clean:
#	rm -rf k-framework
	rm -rf k-framework/dist/bin/java/k3jar k-framework/dist/bin/java/JKrun.jar
	
