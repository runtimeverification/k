// tagfile1.c
// first half of a tagfile tester

// perfectly ordinary definition
int foo(int x)
{
  return x+7;
}

#ifdef STATIC_FUNC
// wrong function type
typedef void (*VoidFn)();

// static function definition that will provoke a descriptor
static int bar(int *p)
{
  VoidFn vf;
  vf = (VoidFn)bar;
  return *p;
}
#endif // STATIC_FUNC
