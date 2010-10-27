// PR594

struct X {
  int Q :6;
   int A : 4;
   int Z : 22;
};

void test(struct X *P, int A) {
   P->A = A;
}

int main() {
  union {
    int Y;
    struct X Z;
  } U;
  U.Y = ~0;
  test(&U.Z, 0);
  printf("%x\n", U.Y);
  return 0;
}
