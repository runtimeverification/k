// Copyright (c) 2014 K Team. All Rights Reserved.
/*
 * Function average computes the integer average of three natural numbers.
 */


#include <stdio.h>


int average(int x, int y, int z)
//@ rule <k> $ => return (x + y + z) / 3; ...</k>
{
  int sum;
  sum = x + y + z;
  return sum / 3;
}
