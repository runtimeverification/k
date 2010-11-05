#include "../small1/testharness.h"
#include "../small1/testkinds.h"

// NUMERRORS 3

struct foo {
  int a[8];
  int *b;
} gfoo;

struct bar {
  int a[8];
  int *b;
};

#if ERROR == 2
struct s1 { 
  int a[8];
  int *b;
} * s1;
struct s2 {
  int *c;
  int d[8];
} * s2; 
#endif

#if ERROR == 3
struct s_with_index {
  int __INDEX arr[8] __INDEX;
} * s1;

struct s_with_non_array {
  int a,b,c,d,e,f,g,h;
} * s2;  
#endif

int main() {
  int * __INDEX p = & gfoo.a[2]; // Force gfoo.a to have a length

  // This should be Ok, but pbar->b is gfoo.a[7]
  struct bar *pbar = (struct bar*)&gfoo;

  pbar->b = 0; 
  gfoo.a[7] = 5;

  printf("Pointer is %lx\n", (unsigned long)pbar->b);
  *(pbar->b) = 0; //ERROR(1): Null

  s1 = s2; if (HAS_KIND(s1, WILD_KIND)) E(2); // ERROR(2):Error

#if ERROR == 3
  s1 = s2; // ERROR(3): compared with a non-array
#endif

  SUCCESS;
}
