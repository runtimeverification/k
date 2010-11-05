#include "testharness.h"

int main(void) {
     int x = 1, y = 5, z = 0;
     asm("movl %[in1], %[out] \n addl %[in2], %[out]"
       : [out] "=r" (z) : [in1] "m" (x), [in2] "m" (y) );

     if(z != 6) E(1);
     return 0;
}

