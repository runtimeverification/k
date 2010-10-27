#include <stdio.h>

struct fun
{
  int x;
} a  = { 32 };

void pfun2(struct fun **z)
{
}

void pfun(struct fun *z)
{
  pfun2(&z);
  printf("%d\n", z->x);
}

int main(int argc, char **argv)
{
  pfun(&a);
  return 0;
}
