
int foo(); // Forward declaration

struct bar {
  int x, y;
};

int (*pfoo)() = (int (*)())foo;

// Now the real declaration
int foo(struct bar *a) {
  return a->x + a->y;
}

