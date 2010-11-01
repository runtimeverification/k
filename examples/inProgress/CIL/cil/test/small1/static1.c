int foo()
{
  static int x = 0;
  return x;
}

int bar()
{
  static int x = 5;
  return x;
}
