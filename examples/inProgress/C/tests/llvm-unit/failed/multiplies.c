#include "helpers.h"

#define ARRAYSIZE 100000
double TheArray[ARRAYSIZE] __attribute__((aligned));

#define ProcessArray(VECTY) {     \
  VECTY V = (VECTY)((v4i32){0,0,0,0}); \
  VECTY *AP = (VECTY*)TheArray;   \
  IV vu;                          \
  for (j = 0; j < 1000; ++j) \
  for (i = 0; i != sizeof(TheArray)/sizeof(VECTY); ++i) \
    V *= AP[i];    \
  vu.V = (v4i32)V;        \
  printIV(&vu);    \
}


int main(int argc, char **Argv) {
  unsigned i, j;
  for (i = 0; i < ARRAYSIZE; ++i)
    TheArray[i] = i*12.345;

  ProcessArray(v16i8);
  ProcessArray(v8i16);
  ProcessArray(v4i32);
  ProcessArray(v2i64);
  
  // These break native gcc.  :(
#if 0
  ProcessArray(v4f32);
  ProcessArray(v2f64);
#endif
  return 0;
}

