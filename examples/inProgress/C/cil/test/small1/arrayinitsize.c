// arrayinitsize.c
// from sac at stevechamberlain dot com
//
// an initializer of an array with unknown size implicitly
// specifies the size (ANSI C, 6.7.8, para 22)
//
// NOTE: gcc-2.x does not support this, so the test harness
// does not try to pass it through gcc before CIL

void abort();

struct X
{
  int a;
  int b;
  int z[];
};

struct X x = { .b = 40, .z = {3,4} };

int main ()
{
  if (x.b != 40)
    abort ();

  // sm: my reading of the spec says this should work, but gcc-3.3
  // does not like it (it *does* work in CIL)
  #if 0
  if (sizeof(x.z) / sizeof(x.z[0]) != 2)
    abort ();
  #endif // 0

  return 0;
}
