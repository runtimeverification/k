/*
 * The program below accesses a location, 1000, which is not allocated.
 * gcc compiles it, but the generated binary yields a segmentation fault.
 * MatchC's error message shows how it got stuck on attempting to "derive"
 * (i.e., make available) memory location 1000, in order to read an int from it.
 */


#include <stdio.h>


int main()
{
  int *x;
  x = (int *) 1000;
  printf("%d", *x);
}
