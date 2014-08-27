// Copyright (c) 2014 K Team. All Rights Reserved.
/*
 * Function comm_assoc checks that function f is commutative and associative.
 */

#include <stdio.h>


int f(int x, int y)
{
  return x + y + x*y;
}

int comm_assoc(int x, int y, int z)
//@ rule <k> $ => return 1; ...</k>
{
  return f(x,y) == f(y,x) && f(x,f(y,z)) == f(f(x,y),z);
}
