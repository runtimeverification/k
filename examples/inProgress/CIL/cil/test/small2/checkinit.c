// Checking of initialization code
#include "../small1/testharness.h"
#include "../small1/testkinds.h"

// NUMERRORS 6

//Prevent inlinging of these functions.  We want to make sure their
//stack frames overlap.
#if __GNUC__ >= 3
#define NOINLINE __attribute__((noinline))
#else
#define NOINLINE
#endif


// Fill the stack with values that are invalid as pointers
void dirtyStack() NOINLINE {
  int i, frame[1024];
  for(i=0;i<sizeof(frame)/ sizeof(int);i++) {
    frame[i] = i;
  }
}


int foo() NOINLINE {
  int *p;
  if(p == 0) E(1);//ERROR(1):Error 1

  // Initialization of structures
#if 2 <= ERROR && ERROR <= 3
  {
    struct str {
      int *f1;
      struct {
        int *i2;
        int i3;
      } f2;
      int *f3;
    } l;
    // All pointers must have been initialized
    if(l.f1 == 0 && l.f2.i2 == 0 && l.f3 == 0) E(2); //ERROR(2):Error 2
    // But the integers should not be initialized.
    // If this test fails then we are probably inserting too much
    // initialization code
    if(l.f2.i3 != 0) E(3); //ERROR(3):Error 3
  }
#endif

  // Initialization of arrays
#if 4 <= ERROR && ERROR <= 5
  {
    int *a[4];if(a[0] == 0 && a[1] == 0 && a[2] == 0 && a[3] == 0) E(4);//ERROR(4):Error 4
    struct s { int *a[2]; } l;if(l.a[0] == 0 && l.a[1] == 0) E(5);//ERROR(5):Error 5
  }
#endif

  // Initialization of unions
#if 6 <= ERROR && ERROR <= 7
  {
    union { int *a, *b[2]; } l;if(l.a == 0 && l.b[0] == 0 && l.b[1] == 0) E(6);//ERROR(6):Error 6
  }
#endif
  
  // Initialization of metadata for pointers
}

int main() {
  dirtyStack();
  return foo();
}
