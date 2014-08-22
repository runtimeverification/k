// Copyright (c) 2014 K Team. All Rights Reserved.
/*
 * Function maximum computes the maximum value between two natural numbers.
 */


#include <stdio.h>


int maximum(int x, int y)
//@ rule <k> $ => return maxInt(x, y); ...</k>
{
  if (x < y) return y;
  return x;
}
