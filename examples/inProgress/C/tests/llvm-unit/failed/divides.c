#include <stdio.h>
typedef unsigned  uvec __attribute__ ((__vector_size__ (16)));
typedef int  svec __attribute__ ((__vector_size__ (16)));
void testuvec(uvec *A, uvec *B, uvec *R) { *R = *A / *B; }
void testsvec(svec *A, svec *B, svec *R) { *R = *A / *B; }

typedef union {
  svec V;
  int A[4];
} SV;

typedef union {
  uvec V;
  unsigned A[4];
} UV;

int main(int argc, char**argv) {
  SV S1, S2, S3;
  UV U1, U2, U3;
  S1.A[0] = S2.A[0] = 2;
  S1.A[1] = S2.A[1] = -3;
  S1.A[2] = S2.A[2] = 5;
  S1.A[3] = S2.A[3] = -8;
  U1.A[0] = U2.A[0] = 2;
  U1.A[1] = U2.A[1] = 3;
  U1.A[2] = U2.A[2] = 5;
  U1.A[3] = U2.A[3] = 8;
  testuvec(&U1.V, &U2.V, &U3.V);
  testsvec(&S1.V, &S2.V, &S3.V);

  printf("U3.V = <%u %u %u %u>\n", U3.A[0], U3.A[1], U3.A[2], U3.A[3]);
  printf("S3.V = <%u %u %u %u>\n", S3.A[0], S3.A[1], S3.A[2], S3.A[3]);
  return 0;
}
