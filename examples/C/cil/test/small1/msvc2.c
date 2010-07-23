
#include "testharness.h"

// This must be run with Visual C. NET

typedef __w64 int t1;
typedef int __w64 t2;


int main() {
  t1 x = 5;
  t2 y = 6;

  return y - x - 1;
}
