#include <stdio.h>

struct fun {
  int x, y;
};

struct fun d;
struct fun *c = &d;

int f(void)
{
  c->x = 11;
  d.x = 12;

  return c->x + d.x;
}

int main(int argc, char **argv)
{
  int zz = f();
  printf("%d\n", zz);
  return 0;
}
