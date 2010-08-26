#include "testharness.h"

int x;


//static void exit(int unused) { }

int main() {
 char p[3];

 //here, p[0] is changed by the assignment.  So don't reevaluate p+p[0] 
 //afterwards
 p[0] = 0;
 p[1] = 2;
 p[2] = 0;
 if (*(p + p[0]) = p[1]) {
   x = 1;
 } else {
   E(1) 
 }

 p[0] = 0;
 p[1] = 2;
 p[2] = 5;
 if ((*(p + p[0]) = p[1]) != 2) { E(2)}

 p[0] = 0;
 p[1] = 2;
 p[2] = 5;
 if ((p[p[0]] = p[1]) != 2) { E(5) }

 p[0] = 1;
 p[1] = 2;
 p[2] = 5;
 if ((p[0] = p[p[0]]) != 2) { E(8) }

 SUCCESS;
 return 0;
}


