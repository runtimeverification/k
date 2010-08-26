// Just one file

// This declaration cannot be dropped even though foo2 will be dropped
static __inline__ int foo2(int x);


int main() {
  void *p = foo2;
  return foo2(5);
}

// This definition will be kept since it is the first
static __inline__ int foo1(int x) {
  return x - 5;
}

// This will be dropped
static __inline__ int foo2(int x) {
  return x - 5;
}
