// mergeinline1.c
// hypothesis about fill_n_... problem

// prototype
static long *fill();

// call
int foo()
{
  long *w = fill();
  return (int)(*w);
}

// inline definition
// (remove "__inline" to work around the bug)
__inline static long *fill()
{
  return 0;
}

int main()
{
  return 0;
}
