// combine_samefn_1.c
// test merging two source files, each of which contain a definition
// of a given function, but those definitions are identical (up to
// alpha renaming of locals/params)
                               
// testing --mergeKeepAnnotations
#pragma ccuredpoly("some_poly_fn")

// repeated function
int foo(int xxx)
{
  int yyy = xxx + 3;    // 8
  int z = yyy + xxx;    // 13
  return z + xxx;       // 18
}


int myglobal __attribute__((mayPointToStack)) = 3;


// give two inlines, which look like results of merging
__inline static int func()
{
  return 3;
}

__inline static int func___0();
__inline static int func___0()
{
  return 3;
}


// defined in combine_samefn_2.c
int otherFunc();


int main()
{
  int ret = func() + func___0() - 6;    // 0
  ret += foo(5) - 18 + myglobal - 3;    // 0
  ret += otherFunc() - 3;               // 0
  return ret;
}

