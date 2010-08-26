// mergestruct1.c
// test merging of structures whose field names differ

struct A {
  int x;
};
                            
// make A's type part of the interface
extern struct A *connection;          

// decl of foo()
int foo();

// refer to A::x
int foo()
{
  if (connection) {
    return connection->x;
  }
  else {
    return 3;
  }
}

// unrelated: test merging of 'unsigned char' and 'signed char'
unsigned char sharedChar;
