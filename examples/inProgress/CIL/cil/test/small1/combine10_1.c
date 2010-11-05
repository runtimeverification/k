/* We have 3 files. First defines g1, second g2, and third refers to both g1 
 * and g2. */

struct foo {
  struct foo * left, * right;
  int x;
} g1;
