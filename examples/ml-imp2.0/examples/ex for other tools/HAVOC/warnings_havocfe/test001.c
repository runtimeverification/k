#include "../../../include/havoc.h"

// Example to illustrate the various errors and their association
// with the uninterpreted tags in the C programs

typedef int *PINT;

typedef struct _FOO FOO, *PFOO;

typedef struct _BAR{
  int f;
  int g;
  int h;
  PFOO i;
} BAR, *PBAR;

typedef struct _FOO{
  int a;
  int b;
  int c;
  PBAR d;
  BAR e;
} FOO, *PFOO;


void Test1_bad(PFOO x, PBAR y)
{
  x->a = 1; //get an error showing that deref object is non-null
}

__requires(x != 0)
     __modifies (&x->a)
void Test2_bad(PFOO x)
{
  __hv_assert(__allocated(&x->a));
  x->a = 1; //get an error showing that deref ptr is non-allocated

}

__requires(x != 0)
     __modifies (&x->d)
void Test3_bad(PFOO x, PBAR y)
{
  x->d = (PBAR)10; //get a type safety violation
}

__requires(x != 0)
void Test4_bad(PFOO x, PBAR y)
{
  x->d = y;
} // get modifies violation


__requires(x != 0)
     __modifies (&x->a)
void Test5_bad(PFOO x, PBAR y)
{
  x->a = 1;
  __hv_assert(x->a == 5); // get assertion violation
}


__ensures (__return == n) //ensures violation of this postcondition
int Test6_bad(int n)
{

  int x = 0;


  return x;
}

void Test7_bad(PFOO x)
{
  Test5_bad(x,0); //precondition violation for Test5
}

__requires (n > 0)
__ensures (__return == n)
     int Test7_good(int n) // no errors
{ 

  int x = 0;

  __loop_invariant(
		   __requires (x <= n) 
		   )
  while (x < n){
    x++;
  }

  return x;
}

__requires (n > 0)
__ensures (__return == n)
int Test8_bad(int n)
{

  int x = 0;

  __loop_invariant(
		   __requires (x == n) //loop invariant might not hold on entry
		   )
  while (x < n){
    x++;
  }

  return x;
}

__requires (n > 0)
__ensures (__return == n)
int Test9_bad(int n)
{

  int x = 0;

  __loop_invariant(
		   __requires (x < n) //loop invariant might not be maintained
		   )
  while (x < n){
    x++;
  }

  return x;
}

__requires (x->y == 1) // annotation error
void Test10_bad(PFOO x)
{
  return;
}


