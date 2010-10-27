#include <altivec.h>
#include <stdio.h>

typedef union {
 float f[4];
 vector float v;
} floatToVector;


void test(float F, vector float *R) {
   floatToVector FTV;
   FTV.f[0] = F;
   *R = (vector float) vec_splat((vector unsigned int)FTV.v, 0);
}

void test2(float F, vector float *R) {
   *R = (vector float)(F);
}
void test2a(float F, vector float *X, vector float *R) {
   *R = (vector float)(F) + *X;
}


int main() {
  floatToVector X;
  int i;
  test(12.34, &X.v);

  printf("%f %f %f %f\n", X.f[0], X.f[1], X.f[2], X.f[3]);
}
