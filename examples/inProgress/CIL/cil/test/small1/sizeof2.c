#include "testharness.h"

int main() {
  if(sizeof((char)0) != 1)  E(1);

  if(sizeof((short)0) != 2)  E(2);

  SUCCESS;
}
