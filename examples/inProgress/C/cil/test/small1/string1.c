#include "testharness.h"


#ifndef __RWSTRING
#define __RWSTRING
#define __FSEQN
#endif

// an empty string; can't just use a string literal, because writing
// into C literals is undefined (and produces segfault on gcc/linux)
char empty[1] = { 0 };

int main() {
  char * __RWSTRING p = empty;  // A pointer to an empty string
  char * __FSEQN pp;
  
  // Overwrite the zero.  When handling strings specially,
  // CCured will fail here.
  *p = '1';

  // Now convert it to a FSEQ. Will call strlen which will fail
  pp = (char * __FSEQN)p;

  pp ++; // This should go outside of the string
  *pp = 0; // Bang

  SUCCESS;
  
}
