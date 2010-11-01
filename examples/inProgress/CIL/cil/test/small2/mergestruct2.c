// mergestruct2.c
// other half of mergestruct1.c

struct B {
  int y;
};

// connect A and B
struct B *connection;

// refer to B::y
int main()
{
  int whatever;

  if (connection) {
    whatever = connection->y;
  }
  whatever += foo();    // for the heck of it
  
  return whatever-whatever;
}

// unrelated: test merging of 'unsigned char' and 'signed char'
// (I edit this to introduce inconsistency..)
unsigned char sharedChar;
