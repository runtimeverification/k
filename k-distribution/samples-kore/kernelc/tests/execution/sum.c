// Copyright (c) 2014 K Team. All Rights Reserved.
#include <stdio.h>


int sum(int n)
{
  int s;

  s = 0;
  while (n > 0) {
    s = s + n;
    n = n - 1;
  }

  return s;
}


int main()
{
  int s;

  s = sum(100);
  printf("The sum for the first 10 natural numbers: %d\n", s);

  return 0;
}

