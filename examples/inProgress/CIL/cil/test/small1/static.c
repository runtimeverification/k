#include "testharness.h"

int counter() {
    static int counter = 18;
    counter = counter + 1;
    return counter;
}


int s1= 17;

int sets1() {
  static int s1 = 5; // Our own private copy
  static int s2;
  
  static int counter = 29; // Try again

  s2 ++;
  
  return s1 + counter;
}

static int s2;


int main() {
  s2 = 28;
  
  if (counter() != 19) E(1);
  if (counter() != 20) E(2);
  if (sets1() != 34) E(3);

  // Make sure that we use two separate s1
  if(s1 != 17) E(4);

  // Make sure we use two separate s2
  if(s2 != 28) E(5);
  
  SUCCESS;
}
