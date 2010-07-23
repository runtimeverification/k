#include "testharness.h"

int main() {
  int a = 0, b = 10;
  int * pi;

  // Comma expressions
  (a++, b) ++; // a = 1, b = 11

  a += b;     // a = 12, b = 11

  if(a != 12 || b != 11) E(1)
  
  (a++, b) = 5; // a = 13, b = 5

  if(a != 13 || b != 5) E(2)
  
  pi = & (a, b); *pi += 4; // a = 13 , b = 9

  if(a != 13 || b != 9) E(3)


  // Conditional expressions

  (a > 12 ? a : b) += 5; // a = 18, b = 9
  
  if(a != 18 || b != 9) E(4)

  (a < 16 ? b : a) = 7; // a = 7, b = 9
  
  if(a != 7 || b != 9) E(5)

  pi = & (a < 12 ? a : b); *pi += 4; // a = 11, b = 9

  if(a != 11 || b != 9) E(6)

  // Casts

  {
    double *pa = (double*)16;
    double *pb;
    
    pa += ((int)pb = 8); // pb = (double*)8; pa += (int)8

    if((int)pa != 16 + 8 * sizeof(double) || (int)pb != 8) E(7)
    
    (int)pa += 5; // pa = (int)pa + 5

    if((int)pa != 16 + 8 * sizeof(double) + 5) E(8)
  }

  SUCCESS;
  return 0;
}
