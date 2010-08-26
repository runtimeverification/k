#include "testharness.h"

int __finite (double __x)
{
  return (__extension__
	  (((((union { double __d; int __i[2]; }) {__d: __x}).__i[1]
	     | 0x800fffffu) + 1) >> 31));
}

int main() {
  double inf = 10000000000.0;
  double old;
  
  if(! __finite(2.0)) E(1);

  do { // Create an infinity
    old = inf;
    inf *= inf;
  } while(old != inf);

  if(__finite(inf)) E(2);

  SUCCESS;
}
