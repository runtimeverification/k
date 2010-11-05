
typedef struct foo *PFOO;

typedef struct foo {
  int x;
  int z; /* This is a new field */
  PFOO y;
} *PTR;

PTR g2;

int main2() {
  int *d = & g2->z; /* Make sure we can refer to it */
  return 0;
}
