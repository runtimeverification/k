#include "../small1/testharness.h"

#define NUMERRORS 2

char * global;

int notmain() {
  char loc;
  // We check that the __checkStackBottom is not too lenient
  global = &loc; //ERROR(2):STORE_SP
}

int main(int argv, char **argv, char **envp) {
  char mainloc;
  // We should be able to store mainloc
  global = & mainloc; E(1); // ERROR(1):Error 1

  // We should be able to store argv
  global = *argv; E(2); // ERROR(2):Error 2

  // And envp
  global = *envp; E(3); // ERROR(3):Error 3

  SUCCESS;
}  
