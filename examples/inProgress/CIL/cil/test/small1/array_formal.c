#include "testharness.h"

//Test for arrays as function parameters.

int foo(int n, int ra[2*n]) {
  printf("sizeof(ra) = %d.  sizeof(*ra) = %d\n", sizeof(ra), sizeof(*ra));
  if (sizeof(ra) != sizeof(int*)) E(1);
  if (sizeof(*ra) != sizeof(int)) E(2);
  return n;
}

// Here, ra has type int (*)[100].  (Pointer to int[100])
int test(int n, int ra[5][100]) {
  printf("sizeof(ra) = %d.  sizeof(*ra) = %d\n", sizeof(ra), sizeof(*ra));
  if (sizeof(ra) != sizeof(int*)) E(11);
  if (sizeof(*ra) != 100*sizeof(int)) E(12);
  return n;
}

// Again, ra has type int (*)[100].
int test2(int n, int ra[n][100]) {
  printf("sizeof(ra) = %d.  sizeof(*ra) = %d\n", sizeof(ra), sizeof(*ra));
  if (sizeof(ra) != sizeof(int*)) E(21);
  if (sizeof(*ra) != 100*sizeof(int)) E(22);
  return n;
}

// Here, *ra has type int[n], so sizeof(*ra) == 4*n.
// But CIL doesn't support arrays with non-constant sizes.
/*
int test3(int n, int ra[5][n]) {
  printf("sizeof(ra) = %d.  sizeof(*ra) = %d\n", sizeof(ra), sizeof(*ra));
  if (sizeof(ra) != sizeof(int*)) E(31);
  if (sizeof(*ra) != n*sizeof(int)) E(32);
  return n;
}
*/

int main() {
  foo(10,0);
  test(10,0);
  test2(10,0);
  SUCCESS;
}
