// boxing sizeof?

#include <stdio.h>   // printf
#include <string.h>  // memset

struct S {
  int *x;
};

int main()
{
  //printf("sizeof is %d\n", sizeof(struct S));
  memset(NULL, 0, sizeof(struct S));
  //return sizeof(struct S);
  return 0;
}
