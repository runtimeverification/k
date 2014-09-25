/*
 * Function f() can only be called directly or indirectly by function h().
 * In other words, the specification of f() states that h must be in the stack.
 */


#include <stdio.h>


void f()
/*@ rule <k> $ => return; ...</k> <stack> S </stack>
    if in(h,ids(S)) */
{
}

void g()
{
  f();
}

void h()
{
  g();
}

int main()
{
  h();
  // Verification fails if you uncomment the next call
  //g();
  h();
}


//@ var S : ListItem

