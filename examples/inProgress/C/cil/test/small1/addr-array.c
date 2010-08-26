#include "testharness.h"

int main() {

  int a[10];

  int (* pa)[10]; // pointer to array
  
  int m[4][7];
  
  // (&a) is a pointer to an array of 10 integers,
  // a is a pointer to integer
  if ((int)((&a)+1) != (int)(a+10))  E(1);

  pa = & a;
  if(& (pa[0][5]) != & a[5]) E(2);
           
  if((char*)(&m + 1) != ((char*)m) + 4 * 7 * sizeof(int)) E(3);

  if((char*)(&(m[2])) != (char*)(m + 2)) E(4);
  
  SUCCESS;
}
