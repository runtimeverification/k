/* This test checks to make sure that LLI and the JIT both implement at_exit 
 * handlers correctly.
 */

#include <stdlib.h>
#include <stdio.h>

static void foo() {
  printf("Exiting!\n");
}

int main() {
  atexit(foo);
  printf("in main\n");
  return 0;
}
