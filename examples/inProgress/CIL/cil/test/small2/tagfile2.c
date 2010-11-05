// tagfile2.c
// second half of a tagfile tester

// external decl of function in tagfile1.c
int foo(int x);

typedef void (*VoidFn)();

int main()
{
  VoidFn tagMaker;
  int x;

  tagMaker = (VoidFn)&foo;      // make CCured tag 'foo'
  x = foo(3);                   // but call it normally

  return x-10;                  // should be 0
}


#ifdef STATIC_FUNC
// static function definition that will provoke a descriptor
static int bar(int *p)
{
  VoidFn vf;
  vf = (VoidFn)bar;
  return *p;
}
#endif // STATIC_FUNC
