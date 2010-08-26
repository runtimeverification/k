#include <stdio.h>

struct fun { int x, y; struct { int a, b; } z; } a = { 1, .z = { 33, 44 } };

int main(int argc, char **argv)
{
  printf("hello world %d %d %d\n", a.x, a.y, a.z.b);
  return 0;
}
