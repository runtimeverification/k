//Shorter version of ilog2 from the linux kernel.
//This tests for an exponential-time bug in cabs2cil's handling of ?:

#define ilog2(n)                                \
(                                               \
       __builtin_constant_p(n) ? (             \
               (n) < 1 ? -1 :     \
               (n) & (1ULL << 31) ? 31 :       \
               (n) & (1ULL << 30) ? 30 :       \
               (n) & (1ULL << 29) ? 29 :       \
               (n) & (1ULL << 28) ? 28 :       \
               (n) & (1ULL << 27) ? 27 :       \
               (n) & (1ULL << 26) ? 26 :       \
               (n) & (1ULL << 25) ? 25 :       \
               (n) & (1ULL << 24) ? 24 :       \
               (n) & (1ULL << 23) ? 23 :       \
               (n) & (1ULL << 22) ? 22 :       \
               (n) & (1ULL << 21) ? 21 :       \
               (n) & (1ULL << 20) ? 20 :       \
               (n) & (1ULL << 19) ? 19 :       \
               (n) & (1ULL << 18) ? 18 :       \
               (n) & (1ULL << 17) ? 17 :       \
               (n) & (1ULL << 16) ? 16 :       \
               (n) & (1ULL << 15) ? 15 :       \
               (n) & (1ULL << 14) ? 14 :       \
               (n) & (1ULL << 13) ? 13 :       \
               (n) & (1ULL << 12) ? 12 :       \
               (n) & (1ULL << 11) ? 11 :       \
               (n) & (1ULL << 10) ? 10 :       \
               (n) & (1ULL <<  9) ?  9 :       \
               (n) & (1ULL <<  8) ?  8 :       \
               (n) & (1ULL <<  7) ?  7 :       \
               (n) & (1ULL <<  6) ?  6 :       \
               (n) & (1ULL <<  5) ?  5 :       \
               (n) & (1ULL <<  4) ?  4 :       \
               (n) & (1ULL <<  3) ?  3 :       \
               (n) & (1ULL <<  2) ?  2 :       \
               (n) & (1ULL <<  1) ?  1 :       \
               (n) & (1ULL <<  0) ?  0 :       \
          -1                 \
      ) :          \
      0   )



int main() {
  int log = ilog2(63);
  printf("%d\n", log);
  return 0;
}
