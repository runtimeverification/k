#include "testharness.h"

#include <stdio.h>


int main() {
  char buffer[16]; // Plenty of space
  double d = 7.75;

  sprintf(buffer, "%5.2f", d); // Make sure we print this as a double

  printf("The buffer is: %s\n", buffer);
  
  if(buffer[0] != ' ' || buffer[1] != '7' || buffer[2] != '.') E(1);

  SUCCESS;
}
