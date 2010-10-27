#include <stdio.h>

struct fun { int x, y; double z; } a = { 1 };

int main(int argc, char **argv)
{
  printf("hello world %d %d %d\n", a.x, a.y, (int)(a.z *1000));
  return 0;
}
