#include "../small1/testharness.h"

// NUMERRORS 4

int one; // Just to hide the arithemtic from CCured

typedef struct { int i1, i2; } two_int;

two_int g;

// Tests for FSEQ and FSEQN
#ifdef ERROR == 0
  #define P_KIND __FSEQ
#elif ERROR == 1
  #define P_KIND __FSEQ
#elif ERROR == 2
  #define P_KIND __FSEQN
#elif ERROR == 3
  #define P_KIND __SEQ
#else
  #define P_KIND __SEQN
#endif

// Converts without seeing in
int * P_KIND safeToSeq(two_int * __SAFE in) {
  // Will convert to { in, in + 8bytes }, if the bug is present
  // It should check first that in is non ZERO
  return (int*)in;
}


int test_fseq() {
  int *f = safeToSeq(&g);
  int dummy = f[one]; // Make sure f is FSEQ
#if ERROR >= 3
  int dummy2 = *(f + one); // Make it SEQ
#endif  
  // Now use the same function to convert the number 0
  // The bug is that we return the pointer {0, 8}
  // Bad cannot be SAFE of else we'll fail the Non-pointer test
  int * P_KIND bad = safeToSeq(0);
  // We can increment bad and read
  // ERROR(1):Non-pointer
  // ERROR(2):Non-pointer
  // ERROR(3):Non-pointer
  // ERROR(4):Non-pointer
#if ERROR > 0
  int res = bad[1];
#endif  
  return 0;
}


int main() {
  one = 1;
  test_fseq(); 
  SUCCESS;
}

