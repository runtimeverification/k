#include "helpers.h"

v4f32 test0001(float a) {
  return (v4f32){a, 0.0, 0.0, 0.0};
}

v4f32 test0010(float a) {
  return (v4f32){0.0, a, 0.0, 0.0};
}

v4f32 test0100(float a) {
  return (v4f32){0.0, 0.0, a, 0.0};
}

v4f32 test1000(float a) {
  return (v4f32){0.0, 0.0, 0.0, a};
}

v4f32 test0011(float a, float b) {
  return (v4f32){a, b, 0.0, 0.0};
}

v4f32 test0101(float a, float b) {
  return (v4f32){a, 0.0, b, 0.0};
}

v4f32 test1001(float a, float b) {
  return (v4f32){a, 0.0, 0.0, b};
}

v4f32 test0110(float a, float b) {
  return (v4f32){0.0, a, b, 0.0};
}

v4f32 test1010(float a, float b) {
  return (v4f32){0.0, a, 0.0, b};
}

v4f32 test1100(float a, float b) {
  return (v4f32){0.0, 0.0, a, b};
}

v4f32 test0111(float a, float b, float c) {
  return (v4f32){a, b, c, 0.0};
}

v4f32 test1011(float a, float b, float c) {
  return (v4f32){a, b, 0.0, c};
}

v4f32 test1101(float a, float b, float c) {
  return (v4f32){a, 0.0, b, c};
}

v4f32 test1110(float a, float b, float c) {
  return (v4f32){0.0, a, b, c};
}

int main(int argc, char **argv) {
  int i, j;
  v4f32 x = {0.0f, 0.0f, 0.0f, 0.0f};
  v4f32 y = {0.0f, 0.0f, 0.0f, 0.0f};
  v4f32 z = {0.0f, 0.0f, 0.0f, 0.0f};

#ifdef SMALL_PROBLEM_SIZE
#define LENGTH 2
#else
#define LENGTH 100
#endif

  for (j = 0; j < LENGTH; ++j) {
    x = (v4f32){0.0f, 0.0f, 0.0f, 0.0f};
    y = (v4f32){0.0f, 0.0f, 0.0f, 0.0f};
    z = (v4f32){0.0f, 0.0f, 0.0f, 0.0f};
    for (i = 0; i < 2000000; ++i) {
      x += test0001(1.0);
      x += test0010(1.0);
      x += test0100(1.0);
      x += test1000(1.0);

      y += test0011(1.0, 2.0);
      y += test0101(1.0, 2.0);
      y += test1001(1.0, 2.0);
      y += test0110(1.0, 2.0);
      y += test1010(1.0, 2.0);
      y += test1100(1.0, 2.0);
  
      z += test0111(2.0, 3.0, 1.0);
      z += test1011(1.0, 1.0, 2.0);
      z += test1101(3.0, 2.0, 4.0);
      z += test1110(4.0, 6.0, 1.0);
    }
  }

  printFV(&x);
  printFV(&y);
  printFV(&z);

  return 0;
}
