// Copyright (c) 2014 K Team. All Rights Reserved.
/*
 * Function sum_iterative returns the sum of the first n natural numbers.
 */


#include <stdio.h>


int sum_iterative(int n)
/*@ rule <k> $ => return (n * (n + 1)) / 2; ...</k>
    if n >= 0 */
{
  int s;

  s = 0;
  //@ inv s = ((old(n) - n) * (old(n) + n + 1)) / 2 /\ n >= 0
  while (n > 0) {
    s = s + n;
    n = n - 1;
  }

  return s;
}
