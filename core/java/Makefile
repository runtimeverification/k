all: ioserver wrapper
	jar cf wrapperAndServer.jar -C IOServer/bin . -C Wrapper/bin .
	
ioserver:
	@mkdir -p IOServer/bin
	javac IOServer/src/*/*.java -d IOServer/bin
	jar cfm ioserver.jar IOServer/Manifest.txt -C IOServer/bin .
#jar cf ioserver.jar IOServer/bin/*
#jar cfe ioserver.jar main.Main IOServer/bin/*/*.class
	
wrapper: ioserver
	@mkdir -p Wrapper/bin
	javac Wrapper/src/*/*.java -d Wrapper/bin -cp IOServer/bin/

	