/* A test the tries to produce double renaming */
extern struct foo1 {
  int x;
} x1;

extern struct bar {
  double d;
} x2;

extern double test();


int main() {
  if(x1.x + x2.d != test()) return 1;

  return 0;
}
