#include "testharness.h"

#ifndef CCURED
#define __TAGGED
#endif


int anint1 = 123, anint2 = 456;

int main() {

    {
      struct only_bitfields {
        int bf1 : 1;
        int bf2 : 4;
      };
      
      struct nested1 {
        int i1;
        int *p1;  // These should be left alone when writing tags to b1
        struct only_bitfields b1;
        int *p2;
      } x1 __TAGGED;
      
      x1.p1 = & anint1; x1.p2 = & anint2; 
      x1.i1 = 5; if(x1.i1 != 5) E(1);
      
      x1.b1.bf2 = 4; if(x1.b1.bf2 != 4) E(2);
      
      // Try to read from x1.p1 and x1.p2 make sure they are valid pointers
      if(* x1.p1 != anint1) E(3);
      
      if(* x1.p2 != anint2) E(4);

    }

    {
      struct start_bitfields {
        int bf2 : 4;
        int bf3 : 5;
        int *    ptr2;
      };
      
      struct nested2 {
        int *ptr1;
        struct start_bitfields b2;
      } x2 __TAGGED;
      
      x2.ptr1 = & anint1; x2.b2.ptr2 = & anint2; 
      x2.b2.bf3 = 5; if(x2.b2.bf3 != 5) E(11);
      
      x2.b2.bf2 = 4; if(x2.b2.bf2 != 4) E(12);
      
      // Try to read the pointers to ensure they are valid
      if(* x2.ptr1 != anint1) E(13);
      
      if(* x2.b2.ptr2 != anint2) E(14);
    }


    {
      struct end_bitfields {
        int * ptr1;
        int bf2 : 4;
        int bf3 : 5;
      };
      struct nested3 {
        struct end_bitfields b3;
        int *ptr2;
      } x3 __TAGGED;

      x3.b3.ptr1 = & anint1; x3.ptr2 = & anint2; 
      x3.b3.bf3 = 5; if(x3.b3.bf3 != 5) E(21);
      
      x3.b3.bf2 = 4; if(x3.b3.bf2 != 4) E(22);
      
      // Try to read the pointers to ensure they are valid
      if(* x3.b3.ptr1 != anint1) E(23);
      
      if(* x3.ptr2 != anint2) E(24);
    }
      



  SUCCESS;
}
