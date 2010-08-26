#include "testharness.h"

// Put the sizeof somewhere where CIL will evaluate it
#ifdef _GNUCC
  char a[sizeof(void)] = { 1 };
  #define sizeof_void sizeof(a)
#else
  #define sizeof_void sizeof(void)
#endif

int main() {
  int expected_sz_void = 0;
#ifdef _GNUCC
  // On GCC sizeof(void) = 1
  expected_sz_void = 1;
#endif
  if(sizeof_void != expected_sz_void) E(1);

 SUCCESS; 
}
