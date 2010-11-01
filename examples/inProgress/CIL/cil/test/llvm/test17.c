#include <stdio.h>

int silly(int w)
{
  int a = 7;

  switch (w) {
  case 11:  return 22;
  case 5: a = 9;
  case 6: return a * 7;
  }
  return a;
}

int main(int argc, char **argv)
{
  printf("hello world - %d %d %d %d\n", silly(0), silly(11), silly(5), silly(6));
  return 0;
}
