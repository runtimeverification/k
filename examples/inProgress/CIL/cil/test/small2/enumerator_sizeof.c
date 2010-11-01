// enumerator_sizeof.c
// an example from the CIL docs, this is an enumeration
// where one of the enumerators is a sizeof expression

#include <assert.h>    // assert

enum {
   FIVE = 5,
   SIX, SEVEN,
   FOUR = FIVE - 1,
   EIGHT = sizeof(double)
};

int main()
{ 
  // store the enumerator values in an array, so the
  // optimizer won't get too clever
  int n[10], i;
  n[4] = FOUR;
  n[5] = FIVE;
  n[6] = SIX;
  n[7] = SEVEN;
  n[8] = EIGHT;
  
  for (i=4; i<=8; i++) {
    assert(i == n[i]);
  }

  return 0;
}

