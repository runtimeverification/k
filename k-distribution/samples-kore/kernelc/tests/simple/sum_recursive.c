// Copyright (c) 2014 K Team. All Rights Reserved.
/*
 * Function sum_recursive computes the sum of the first n natural numbers.
 */


#include <stdio.h>


int sum_recursive(int n)
/*@ rule <k> $ => return (n * (n + 1)) / 2; ...</k>
    if n >= 0 */
{
  if (n <= 0) return 0;
  return n + sum_recursive(n-1);
}
