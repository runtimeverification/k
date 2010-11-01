//Test of boolean operators on values larger than int.

#include "testharness.h"

#ifdef _MSC_VER //Microsoft
# define int64_t __int64
#else
# include "sys/types.h"
#endif
int main () {

  int64_t a64, b64;
  float f;
  double d;
  int* p = 0;

  int64_t bignum = 1;	 // compute 2^40 - this would be truncated
  bignum = bignum << 40; // to zero if cast to int (typically)


  a64 = 42;
  b64 = a64 + bignum;
  //a64 = b64 modulo 2^32

  if (a64 == b64) {
    E(1);
  }
  if (a64 >= b64) {
    E(2);
  }
  if ((a64|bignum) == a64)
    E(3);

  if (! bignum) {
    E(5);
  }

  f = 0.125f;
  if (!f)
    E(10);
  if (f >= 0.25f)
    E(11);

  d = 0.125;
  if (d < f || d > f)
    E(12);


  SUCCESS;
}
