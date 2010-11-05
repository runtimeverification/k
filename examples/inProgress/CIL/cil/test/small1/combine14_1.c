/* A tests with function prototypes. We do not want to change the names of 
 * the format arguments of a function to those specified by the prototype. 
 * First the prototype. */
#include "testharness.h"

int protoname1 = 5;
extern int protoname2;

void foo(int protoname1);

void bar(int myname) {
  protoname2 = myname;
}

int main() {
  foo(0); /* Should set protoname1 and protoname2 to 0 */
  if(protoname1 != 0) E(1);
  if(protoname2 != 0) E(2);

  SUCCESS;
}
