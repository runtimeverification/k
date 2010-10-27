#include <stdio.h>
#include <stdint.h>

struct X {
  unsigned char pad : 4;
  uint64_t a : 64;
  uint64_t b : 60;
} __attribute__((packed));

int main (void)
{
  struct X x;
  uint64_t bad_bits;

  x.pad = 255;
  x.a = -1ULL;
  x.b = -1ULL;

  bad_bits = ((uint64_t)-1ULL) ^ *(1+(uint64_t *) &x);
  printf("bad bits: %llx\n", bad_bits);
  return bad_bits != 0;
}
