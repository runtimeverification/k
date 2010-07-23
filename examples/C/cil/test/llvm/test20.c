#include <stdio.h>

struct fun { int x, y; double z; } a = { 1 };

int main(int argc, char **argv)
{
  printf("hello world %d %d %f\n", a.x, a.y, a.z);
  return 0;
}
