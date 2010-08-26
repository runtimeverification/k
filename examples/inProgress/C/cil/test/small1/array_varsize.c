#include "testharness.h"

// Variable-sized arrays
void foo(int n, int a[n]);

int main(void)
{
  int a[40];
  foo(40, a);
  SUCCESS;
}

//Two variable-sized arrays
//In CIL, a is changed to a pointer, and b uses alloca
void foo(int n, int a[n]) {
  
   double b[n];
   a[n-1] = 0;
   b[n-1] = 0.0;
   printf("sizeof(a) = %d, sizeof(b) = %d\n", sizeof(a), sizeof(b));

   //formals should be promoted to pointers (int*, in this case)
   int* p = a;
   p++;
   if (sizeof(a) != sizeof(p)) E(2);

   //locals should keep their array type.  CIL rewrites sizeof(b)
   // as (n * sizeof(*b))
   if (sizeof(b) != (n * sizeof(double))) E(3);
}

