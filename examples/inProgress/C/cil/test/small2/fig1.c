// fig1.c
// program in our paper, figure 1

#include <stdio.h>     // printf
#include <stdlib.h>    // malloc

int **getArray()
{
  int **a = (int**)malloc(100 * sizeof(*a));
  int i;

  for (i=0; i<100; i++) {
    a[i] = (int*) (((i+1) << 1) | 1);         // for the moment, no boxing
  }

  return a;
}


int main()
{
  int **a = getArray();
  int i;
  int acc;
  int **p;
  int *e;

  acc = 0;
  for (i=0; i<100; i++) {
    p = a + i;
    e = *p;
    while ((int)e % 2 == 0) {
      e = *(int**)e;
    }
    acc += ((int)e >> 1);
  }

  printf("acc is %d\n", acc);    // should be 5050
  return 0;
}
