#include <stdlib.h>

//@ ensures *p >= 0
void abs1(int *p) {
  if (*p < 0) *p = -*p;
}

/*@ requires \valid(p)
  @ ensures *p >= 0
  @*/
void abs2(int *p) {
  if (*p < 0) *p = -*p;
}

int main()
{
  return abs(-5);
}
