// oldstyle decls are problematic in themselves?

static int foo(int x);    // right now, 'static' is the problem

int foo(x)
  int x;
{
  return x;
}

int main()
{
  return foo(0);
}
