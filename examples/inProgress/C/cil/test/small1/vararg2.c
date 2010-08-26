
#include <stdio.h>
#include <stdarg.h>

struct vararg_sum {
  int ints;                   /* We only pass ints to this one */
  int *pints;
};
#pragma ccuredvararg("sum", sizeof(struct vararg_sum))

int sum( int descriptor, ... );

#include "testharness.h"

int main( void )
{
  int i1 = 5;
  int i2 = 7;

  /* Call with 3 integers (-1 is used as terminator). */
  if(sum(0xA, 3, &i1, 7, &i2, 0) != 22) E(1);

  SUCCESS;
}



/* Returns the average of a variable list of integers and pointers to 
 * integers. Each bit in the descriptor says what type is the corresponding 
 * argument (1 for pointer). 0 is used as a terminator. */
int sum( int descriptor, ... )
{
   int sum = 0;
   va_list marker;

   va_start( marker, descriptor );     /* Initialize variable arguments. */
   while(1) {
     int next;
     if (descriptor & 1) {
       next = * va_arg (marker, int*);
     } else {
       next = va_arg(marker, int);
     }
     if(!next) return sum;
     sum += next;
     descriptor >>=1;
   }
   va_end(marker);
}
