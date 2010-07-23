#include "testharness.h"
#include <string.h>

int main() {

  int      slen       = strlen(".nfs") + 5;
  char           silly[slen+1];

  slen += 20;

  if(sizeof(silly) != 10) E(1)

  SUCCESS;
}
