
#include <stdio.h>
sum(to, from, count)
     short *to, *from;
     short count;
{
  int i;
  for (i = 0; i != count; ++i)
    *to += *from++;
}

#define NUM 2
int main() {
  short Array[NUM];
  short Sum = 0;
  int i;

  for (i = 0; i != NUM; ++i)
    Array[i] = i;

  sum(&Sum, Array, NUM);

  printf("Sum is %d\n", Sum);
  return 0;
}
