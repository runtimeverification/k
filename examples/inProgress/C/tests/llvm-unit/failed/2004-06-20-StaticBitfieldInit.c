#include <stdio.h>

struct T {
  unsigned X : 5;
  unsigned Y : 6;
  unsigned Z : 5;
};

struct T GV = { 1, 5, 1 };

int main() {
  printf("%d %d %d\n", GV.X, GV.Y, GV.Z);
  return 0;
}
