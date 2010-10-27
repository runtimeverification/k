#include <stdio.h>

int foo(volatile *mem, int val, int c) {
  int oldval = __sync_fetch_and_add(mem, val);
  return oldval + c;
}

int main() {
  volatile int x = 0;
  int y = foo(&x, 1, 2);
  printf("%d, %d\n", y, x);
  y = __sync_val_compare_and_swap(&x, 1, 2);
  printf("%d, %d\n", y, x);
  y = __sync_lock_test_and_set(&x, 1);
  printf("%d, %d\n", y, x);
  return 0;
}
