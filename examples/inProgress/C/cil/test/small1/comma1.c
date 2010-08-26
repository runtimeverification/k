#include "testharness.h"


int to_hex(int x) { return x; }

int main() {

  if(6 != to_hex((5, 6))) E(1);
  
  SUCCESS;
}
  
