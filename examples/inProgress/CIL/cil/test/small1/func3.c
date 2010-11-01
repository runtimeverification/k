
typedef int (*func)();  // Declare this without arguments

int foo(int *x, int z, int *y) {
  return *x + z + *y;
}

int main() {
  int x = 5, y = 7, z = 13;

  func f = foo;

  x = f(&x, &z, &y) - 12 - (int)&z; // Should be 0

  return x + foo(&x, z, &y) - 20;

  
}

