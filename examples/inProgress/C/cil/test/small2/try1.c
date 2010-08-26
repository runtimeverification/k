#include "../small1/testharness.h"

#include <excpt.h>

// NUMERRORS 3

// This is for MSVC
#ifndef _MSVC
error This test works only for MSVC
#endif

int throw() {
  // Simulate a segfault
  { __NOCUREBLOCK
      // We do not want CCured to notice this one
      *((int*)0) = 5;
  }
}

void incr(int *px) {
  *px = 1 + *px;
}

int main() {

  int i = 0;

  __try {
    i ++;
  } __finally {
    i --;
  }

#if ERROR >= 1 && ERROR <= 2
  __try {
    i ++;
    throw (); // ERROR2
  } __except(i +=5, EXCEPTION_EXECUTE_HANDLER) {
    i --;
  }
  if(i == 1) E(1); // ERROR1:Error 1
  if(i == 5) E(2); // ERROR2:Error 2
#endif

#if ERROR >= 3  
  __try {
    __try {
      i ++;
      throw ();
    } __except(i ++, EXCEPTION_CONTINUE_SEARCH) {
      E(3); // Should not get here
    }
  } __except(incr(&i), incr(&i), EXCEPTION_EXECUTE_HANDLER) {
    if(i == 4) E(32); // ERROR3:Error 32
  }
  E(31);
#endif
  
  if(i != 0) E(100); // ERROR0
  
  SUCCESS;
}
     

