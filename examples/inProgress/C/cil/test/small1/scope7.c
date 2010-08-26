#include "testharness.h"

struct packet {
  int (*pfun)(int, char **);
  int *p;
};


int main(int argc, char **argv) {
  struct packet loc = { main, 0 };

  static struct packet glob = { main, 0 };

  if(loc.pfun != glob.pfun) E(1);

  SUCCESS;
  
}
