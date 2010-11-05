// fmtstr.c
// demonstrate a format-string bug

#include <stdio.h>

int main()
{
  char *s = "%d -- bad!\n";
  printf(s);
  return 0;
}
