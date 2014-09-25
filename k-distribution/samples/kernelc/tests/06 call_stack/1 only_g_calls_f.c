/*
 * Function f() can only be called directly by function g().  In other words,
 * the specification of f() states that the head id in the stack must be g.
 * The functions g() and h() have no specifications, which means that there
 * is nothing to prove about them.  The function main() has no specification
 * either, but according to the C semantics it is called when the program
 * starts, so matchC verifies it by default.  Use "//@ skip" in front of a
 * function if you don't want it verified.
 */


#include <stdio.h>


void f()
/*@ rule <k> $ => return; ...</k> <stack> S </stack>
    if hd(ids(S)) = g */
{
}

void g()
{
  f();
}

void h()
{
  g();
  // Verification fails if you uncomment the next call to f(),
  // but it succeeds again if you comment the call to h()
  // in function main() below or skip the function main().
  //f();
  g();
}

int main()
{
  h();
}


//@ var S : ListItem

