struct foo2;

struct foo2 {
  int x;
} x1; /* This will be isomorphic with struct foo1 in file 1 */


struct foo1 { /* This will be isomorphic with struct bar in file 1 */
  double d;
} x2;


double test() {
  return x1.x + x2.d;
}
