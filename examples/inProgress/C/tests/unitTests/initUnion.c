// based on pr19687.c from gcc torture tests
union U
{
  int i;
};

union U2
{
  float f; int i;
};

int main ()
{
  union U t = {};
  union U2 t2 = {};

    if (t.i != 0)
      abort ();
	if (t2.f != 0.0)
      abort ();

  return 0;
}
