#include <emmintrin.h>
#include <stdio.h>

typedef union {
  __m128i V;
  int A[4];
} IV;

static void printIV(IV *F) {
  printf("%08x %08x %08x %08x\n", F->A[0], F->A[1], F->A[2], F->A[3]);
}

int main() {
  __m128i allones = _mm_set1_epi32(0);
  __m128i zeroones, onezeros;
  allones = _mm_cmpeq_epi32(allones, allones);
  zeroones = _mm_srli_epi16(allones, 8);
  printIV((IV*)&zeroones);
  onezeros = _mm_slli_epi16(allones, 8);
  printIV((IV*)&onezeros);
  return 0;
}
