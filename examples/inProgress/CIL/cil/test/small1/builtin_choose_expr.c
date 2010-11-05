#include "testharness.h"

//__builtin_choose_expr is a compile-time version of ?:

int main() {
  char c = 0;
  int i = 1;
  if (sizeof(__builtin_choose_expr(1, c, i)) != sizeof(char)) E(1);
  if (sizeof(__builtin_choose_expr(0, c, i)) != sizeof(int)) E(2);

  int* p =   __builtin_choose_expr(1, &i, 2.0);
  double d = __builtin_choose_expr(0, &i, 2.0);

  //Don't evaluate the i++
  c = __builtin_choose_expr(1, c, i++);
  if (i != 1) E(3)

  //Do evaluate the i++
  c = __builtin_choose_expr(0, c, i++);
  if (i != 2) E(4)

  return __builtin_choose_expr(1, 0, 1);
}
