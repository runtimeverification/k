/* Two identical structures but one uses typedef */
struct foo {
  struct foo * left, * right;
  int x;
} g;

