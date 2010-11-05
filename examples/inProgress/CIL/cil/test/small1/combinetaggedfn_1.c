// combinetaggedfn_1.c
// test problem that arises with --separate when one module
// infers a function must be tagged, but another inferrs
// it should not be tagged

// in this module, foo will be untagged
int foo(int x)
{
  return x+1;
}
