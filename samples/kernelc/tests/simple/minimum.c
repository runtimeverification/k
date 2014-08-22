// Copyright (c) 2014 K Team. All Rights Reserved.
/*
 * Function minimum computes the minimum value between two natural numbers.
 */


#include <stdio.h>


int minimum(int x, int y)
//@ rule <k> $ => return minInt(x, y); ...</k>
{
  if (x < y) return x;
  return y;
}
