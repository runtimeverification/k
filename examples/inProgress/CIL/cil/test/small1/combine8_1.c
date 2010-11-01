#include "testharness.h"

struct foo {
  int x;
  struct googoo * next;
} * g1;


struct googoo {
  double d;
};


int main() {
  SUCCESS; 
}
