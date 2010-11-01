#include "testharness.h"

int main() {
  long w = L'W';      // wide character constant
  char * s =  "W"; 
  int i;

  if (w != s[0]) { E(1); }
  SUCCESS;

}
