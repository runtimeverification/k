/* these first three reference functions were taken from 
 * http://www.hackersdelight.org/HDcode/nlz.cc and
 * http://www.hackersdelight.org/HDcode/ntz.cc
 */
#include <stdio.h>

#define u 99

int nlz10b(unsigned x) {

   static char table[64] =
     {32,20,19, u, u,18, u, 7,  10,17, u, u,14, u, 6, u,
       u, 9, u,16, u, u, 1,26,   u,13, u, u,24, 5, u, u,
       u,21, u, 8,11, u,15, u,   u, u, u, 2,27, 0,25, u,
      22, u,12, u, u, 3,28, u,  23, u, 4,29, u, u,30,31};

   x = x | (x >> 1);    // Propagate leftmost
   x = x | (x >> 2);    // 1-bit to the right.
   x = x | (x >> 4);
   x = x | (x >> 8);
   x = x & ~(x >> 16);
   x = (x << 9) - x;    // Multiply by 511.
   x = (x << 11) - x;   // Multiply by 2047.
   x = (x << 14) - x;   // Multiply by 16383.
   return table[x >> 26];
}

int nlzll(unsigned long long x) {
  if ((x >> 32) == 0)
    return nlz10b(x)+32;
  return nlz10b(x>>32);
}

int pop(unsigned x) {
   x = x - ((x >> 1) & 0x55555555);
   x = (x & 0x33333333) + ((x >> 2) & 0x33333333);
   x = (x + (x >> 4)) & 0x0F0F0F0F;
   x = x + (x << 8);
   x = x + (x << 16);
   return x >> 24;
}

int popll(unsigned long long x) {
  return pop(x) + pop(x >> 32);
}

int ntz8(unsigned x) {

   static char table[64] =
     {32, 0, 1,12, 2, 6, u,13,   3, u, 7, u, u, u, u,14,
      10, 4, u, u, 8, u, u,25,   u, u, u, u, u,21,27,15,
      31,11, 5, u, u, u, u, u,   9, u, u,24, u, u,20,26,
      30, u, u, u, u,23, u,19,  29, u,22,18,28,17,16, u};

   x = (x & -x)*0x0450FBAF;
   return table[x >> 26];
}

/* Work with non-gcc compilers and GCC before 4.0 */
#if !defined(__GNUC__) || __GNUC__ < 4
#define __builtin_clz nlz10b
#define __builtin_popcount pop
#define __builtin_ctz ntz8
#define __builtin_clzll nlzll
#define __builtin_popcountll popll
#define __builtin_ffsl __builtin_ffs
#define ffsl ffs
#endif

int i;
int main(void) {
  long long l;

  /* note: we don't test zero, because the _native_ test will get it
   * wrong (GCC returns garbage for ctz/clz of 0), and the nightly tester
   * will wrongly conclude that CBE and LLC are both failing.
   */
  for(i=10; i<139045193; i*=-3) {
    printf("LLVM: n: %d, clz(n): %d, popcount(n): %d, ctz(n): %d\n",
	i, __builtin_clz(i), __builtin_popcount(i), __builtin_ctz(i));
    printf("REF : n: %d, clz(n): %d, popcount(n): %d, ctz(n): %d\n",
	i, nlz10b(i), pop(i), ntz8(i));
    printf("  ***  \n");
    i++;
  }

  for(l=-10000; l<139045193*10000LL; l*=-3) {
    printf("LLVM: n: %lld, clz(n): %d, popcount(n): %d, ctz(n): %d\n",
	l, __builtin_clzll(l), __builtin_popcountll(l), __builtin_ctz(l));
    printf("REF LO BITS : n: %lld, clz(n): %d, popcount(n): %d, ctz(n): %d\n",
	l, nlzll(l), popll(l), ntz8(l));
    printf("  ***  \n");
    l++;
  }

  // Check some boundary and other cases  for FFS call
  printf("FFS: 0:%d, 1:%d, 2:%d, 7:%d, 1024:%d, 1234:%d i:%d, l:%d\n",
      ffs(0), ffs(1), ffs(2), ffs(7), ffs(1024), ffs(1234), ffs(i), ffsl(l));
  printf("__builtin_ffs: 0:%d, 1:%d, 2:%d, 7:%d, 1024:%d, 1234:%d i:%d l:%d\n",
      __builtin_ffs(0), __builtin_ffs(1), __builtin_ffs(2), __builtin_ffs(7),
      __builtin_ffs(1024), __builtin_ffs(1234), __builtin_ffs(i), __builtin_ffsl(l)); 

  return(0);
}

