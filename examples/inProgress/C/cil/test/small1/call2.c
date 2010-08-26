#include "testharness.h"


int any_int(void) {
   return 3;
}

void main() {
   int tmp = -1;
   unsigned int G;
   // We had a bug that replaced the next two lines with
   // G = any_int ();
   tmp = any_int();
   G = tmp;
   tmp = tmp-3;
   if(tmp != 0) E(1);
   SUCCESS;
}
