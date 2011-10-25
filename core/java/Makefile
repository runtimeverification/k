all: ioserver.jar wrapperAndServer.jar
	
ioserver.jar: $(wildcard IOServer/src/*/*.java) IOServer/Manifest.txt
	@mkdir -p IOServer/bin
	javac -target 1.5 -source 1.5 IOServer/src/*/*.java -d IOServer/bin
	jar cfm ioserver.jar IOServer/Manifest.txt -C IOServer/bin .

wrapperAndServer.jar: ioserver.jar  $(wildcard Wrapper/src/*/*.java) Wrapper/Manifest.txt
	@mkdir -p Wrapper/bin
	javac Wrapper/src/*/*.java -d Wrapper/bin -cp IOServer/bin:jopt-simple-3.3.jar	
	jar cfm wrapperAndServer.jar Wrapper/Manifest.txt -C IOServer/bin . -C Wrapper/bin .
