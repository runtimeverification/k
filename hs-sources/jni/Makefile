SDF_PATH=/home/maude/dist
SDF_LIB=$(SDF_PATH)/lib
SDF_INC=$(SDF_PATH)/include

JAVA_INC=/usr/lib/jvm/java-6-openjdk/include

all: libSglrJNI.so
test: test.c libSglrJNI.so
	gcc -Wall -o test test.c -L. -L/data/dist/lib -lSglrJNI -lsglr -lmept -lErrorAPI -lATerm -lLocationAPI
org_kframework_parser_utils_SglrJNI.h:
	javac org/kframework/parser/utils/SglrJNI.java
	javah -classpath . -jni org.kframework.parser.utils.SglrJNI
libSglrJNI.so: org_kframework_parser_utils_SglrJNI.c org_kframework_parser_utils_SglrJNI.h sdf-wrapper.c
	gcc -Wall -o SglrJNI.o -fpic -I$(JAVA_INC) -c org_kframework_parser_utils_SglrJNI.c
	gcc -Wall -o sdf-wrapper.o -fpic -I$(SDF_INC) -c sdf-wrapper.c
	ar rcs libSglrJNI.a SglrJNI.o sdf-wrapper.o
	gcc -shared -o libSglrJNI.so -Wl,--whole-archive libSglrJNI.a $(SDF_LIB)/libATB.a $(SDF_LIB)/libATerm.a $(SDF_LIB)/libErrorAPI.a $(SDF_LIB)/libLocationAPI.a $(SDF_LIB)/libPTMEPT.a $(SDF_LIB)/libmept.a $(SDF_LIB)/libsglr.a -Wl,--no-whole-archive
clean:
	-rm org_kframework_parser_utils_SglrJNI.h
	-rm SglrJNI.o
	-rm sdf-wrapper.o
	-rm libSglrJNI.so
	-rm libSglrJNI.a
	-rm org/kframework/parser/utils/SglrJNI.class


