// mergeinline2.c
// counterpart to mergeinline1.c

// prototype
static long *fill();

// call
int bar()
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

