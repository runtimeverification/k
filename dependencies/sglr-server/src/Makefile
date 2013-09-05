CFLAGS=-D NDEBUG -I. -I../aterm-2.5/include -I../sdf2-bundle-2.4/include
LDFLAGS=-L../aterm-2.5/lib -L../sdf2-bundle-2.4/lib

SRC=$(sdf-wrapper.c)
OBJS=$(SRC:.c=.o)
BIN=sglr-server
all : $(BIN)
$(BIN) : main.c $(OBJS)
	gcc $(CFLAGS) $(LDFLAGS) -o $(BIN) main.c sdf-wrapper.c $(OBJS) -lsglr -lATerm -lmept -lc -lErrorAPI -lLocationAPI
clean :
	rm -f $(BIN) $(OBJS)
