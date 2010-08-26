#include "testharness.h"




int main() {
  if(((int []){1, 2, 3, 4})[1] != 2) E(1);

  ((int []){1, 2, 3, 4})[1] = 15;
  
  SUCCESS;
}
