#include "../../../include/havoc.h"
#include <stdio.h>

int g;

__requires (x != 0)
__requires (y != 0)
__requires (x != y)

__ensures (*y == __old(*y)) 
__modifies (__old(x))
void foo (int *x, int *y)
{
    *x = 0;

    __loop_invariant(
		__loop_assert(*x <= 100)
		__loop_modifies(__old(x))
		)
      while (*x < 100) {(*x)++; printf("*x = %d\n", *x);}
}

