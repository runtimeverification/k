#include "testharness.h"


void foo(int invok) {
  static const int honour_longs = (4 > 4) || (4 > 4);
  static int bar = 0;
  
  if(invok == 0) {
    if(honour_longs != 0) E(1);
    if(bar != 0) E(2);
    bar = 1;
    return;
  }
  if(bar != 1) E(3);
  return;
}


int main() {

  static int bar = 3;
  foo(0);
  if(bar != 3) E(4);
  foo(1);
  if(bar != 3) E(5);

  SUCCESS;
}
  
