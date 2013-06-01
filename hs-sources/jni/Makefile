all: libSglrJNI.so
test: test.c libSglrJNI.so
	gcc -Wall -o test test.c -L. -L/data/dist/lib -lSglrJNI -lsglr -lmept -lErrorAPI -lATerm -lLocationAPI
libSglrJNI.so: SglrJNI.c SglrJNI.h sdf-wrapper.c
	gcc -Wall -o libSglrJNI.so SglrJNI.c sdf-wrapper.c -shared -fpic -I/usr/lib/jvm/java-6-openjdk/include -I/data/dist/include  -L/data/dist/lib -lsglr -lmept -lErrorAPI -lATerm -lLocationAPI
SglrJNI.h: SglrJNI.class
	javah -jni SglrJNI
SglrJNI.class: SglrJNI.java
	javac SglrJNI.java
clean:
	-rm SglrJNI.h
	-rm SglrJNI.o
	-rm libSglrJNI.so
	-rm SglrJNI.class


