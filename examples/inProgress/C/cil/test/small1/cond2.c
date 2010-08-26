#include "testharness.h"

int calls_to_foo = 0;
int foo() {
  calls_to_foo ++;
  return calls_to_foo;
}

enum
{
  _ISupper = (( 0 ) < 8 ? ((1 << ( 0 )) << 8) : ((1 << ( 0 )) >> 8)) ,	 
  _IScntrl = (( 9 ) < 8 ? ((1 << ( 9 )) << 8) : ((1 << ( 9 )) >> 8)) ,	 
};

int main() {
  static int x = (sizeof(int) == 4) ? (5 && 4) : &main;

  if(x != 1) E(1);

  {
    int *x2 = &main ? : 0;
    if(x2 != &main) E(2);
  }

  {
    int x3 =  foo() ? : 0;
    if(x3 != 1 || calls_to_foo != 1) E(3);
  }
  SUCCESS;
}
