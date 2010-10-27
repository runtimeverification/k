extern int printf(const char*, ...);
void foo( unsigned int i, int array[4]) __attribute__((noinline));
void foo( unsigned int i, int array[4]) {
  unsigned int j;
  for (j=3; j>i; j--)
    array[j] = array[j-1];
  printf("%d %d %d %d %d\n", i, array[0], array[1], array[2], array[3]);
}
main() {
  int array[4], i;
  for (i=0; i<5; i++) {
    array[0] = 5; array[1] = 6; array[2] = 7; array[3] = 8;
    foo(i, array);
  }
  array[0] = 5; array[1] = 6; array[2] = 7; array[3] = 8;
  foo(0xffffffffu, array);
  return 0;
}
