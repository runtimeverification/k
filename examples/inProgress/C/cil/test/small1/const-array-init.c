#include <stdlib.h>

/* We must strip all of the "const" qualifiers in structs that are used for 
 * locals */
struct foo {
  const  int f1;
  struct bar {
    const int f2;
    const int a[8];
  }      b;
};

int main()
{
  const int values[] = { 0 };
  struct foo f = { 1, 2, 3, 4, 5, 6 };
  int x;
  x = values[0];
  exit(0);
}
