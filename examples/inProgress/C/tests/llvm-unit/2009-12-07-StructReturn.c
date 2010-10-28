/* <rdar://problem/7437022> */
/* Just enough complexity to frighten the optimizer and expose a bug
   in an ugly one-file testcase. */
extern int printf(const char * __restrict, ...);
extern void abort(void);
typedef struct {
  float ary[3];
} foostruct;
typedef struct {
  foostruct foo;
  float safe;
} barstruct;
barstruct bar_ary[4];
float * __attribute__ ((__noinline__))
  spooky(int i) {
  bar_ary[i].safe = 142.0;
  return &bar_ary[i].safe;
}
foostruct __attribute__ ((__noinline__))
foobify(void) {
  static barstruct my_static_foo = { {42.0, 42.0, 42.0}, /*safe=*/42.0 };
  return my_static_foo.foo;
}
int
main(int argc, char *argv[]) {
  float *pf = spooky(0);
  /* This should store exactly 96 bits.  Some compilers stored 128
     bits, clobbering beyond the end of the "foo" struct.  */
  bar_ary[0].foo = foobify();
  if (*pf != 142.0) {
    printf("error: store clobbered memory outside destination\n");
    abort();
  }
  return 0;
}
