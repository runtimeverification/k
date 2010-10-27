#include <stdio.h>

typedef float  v4sf __attribute__ ((__vector_size__ (16)));
typedef double v2sd __attribute__ ((__vector_size__ (16)));

// These require legalization.
typedef float  v8sf __attribute__ ((__vector_size__ (32)));
typedef double v8sd __attribute__ ((__vector_size__ (64)));

typedef int    v2i64 __attribute__ ((__vector_size__ (16)));
typedef int    v4i32 __attribute__ ((__vector_size__ (16)));
typedef short  v8i16 __attribute__ ((__vector_size__ (16)));
typedef char   v16i8 __attribute__ ((__vector_size__ (16)));
typedef float  v4f32 __attribute__ ((__vector_size__ (16)));
typedef double v2f64 __attribute__ ((__vector_size__ (16)));

typedef union {
  v4i32 V;
  int A[4];
} IV;

typedef union {
  v4sf V;
  float A[4];
} FV;

typedef union {
  v2sd V;
  double A[2];
} DV;

typedef union {
  v8sd V;
  double A[8];
} D8V;

static void printIV(IV *F) {
	printf("%u %u %u %u\n", F->A[0], F->A[1], F->A[2], F->A[3]);
}

static void printFV(FV *F) {
	printf("%f %f %f %f\n", F->A[0], F->A[1], F->A[2], F->A[3]);
}

static void printDV(DV *D) {
	printf("%g %g\n", D->A[0], D->A[1]);
}

static void printD8V(D8V *D) {
	printf("%g %g %g %g %g %g %g %g\n", D->A[0], D->A[1], D->A[2], D->A[3],
                                            D->A[4], D->A[5], D->A[6], D->A[7]);
}
