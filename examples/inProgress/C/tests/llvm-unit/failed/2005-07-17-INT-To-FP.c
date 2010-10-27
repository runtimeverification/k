// Test the various SINT-TO-FP and UINT-TO-FP conversions.
#include <stdio.h>

int tests[] = {
  0x80000000,
  -123456792,
  -10,
  -2,
  -1,
  0,
  1,
  2,
  10,
  123456792,
  0x7FFFFF80
};

int main() {

  unsigned i;
  // byte boundary tests
  for (i = 0; i < 64; ++i) {
    printf("%d %f, %f, %f, %f\n", i,
           (double)(signed char)(i << 2),            // i8
           (double)(signed short)(i << 10),          // i16
           (double)(signed int)(i << 26),            // i32
           (double)(signed long long)((long long)i << 58ULL));  // i64

    printf("%d %f, %f, %f, %f\n", i,
           (double)(unsigned char)(i << 2),            // i8
           (double)(unsigned short)(i << 10),          // i16
           (double)(unsigned int)(i << 26),            // i32
           (double)(unsigned long long)((unsigned long long)i << 58ULL));  // i64
  }
  // edge case tests
  for (i = 0; i < (sizeof(tests) / sizeof(int)); i++) {
    printf("%d %f, %f, %f, %f\n", i,
                               (double)(unsigned)tests[i],
                               (double)(  signed)tests[i],
                               (float)           tests[i],
                               (float) (  signed)tests[i]);
  }
  return 0;
}
