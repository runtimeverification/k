// Copyright (c) 2014 K Team. All Rights Reserved.
/*
 * Function computing recursively the multiplication of two natural numbers
 * by repeated additions.
 */


#include <stdio.h>


int multiplication_by_addition(int x, int y)
//@ rule <k> $ => return (x * y); ...</k>
{
  if (x == 0) return 0;
  if (x < 0) return -multiplication_by_addition(-x,y);
  return y + multiplication_by_addition(x - 1, y);
}
