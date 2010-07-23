#include <stdio.h>

int a[4][4] = { 0, 4, 7 };

int main(int argc, char **argv)
{
  printf("hello world %d %d %d\n", a[0][1], a[2][2], a[0][3]);
  return 0;
}
