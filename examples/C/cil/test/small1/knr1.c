


int old_function(a, b, c)
     int a, * c;
     int *b;
{
  return a + *b;
}


norettype(int x) {
  return x;
}

norettype_old(x)
     int x;
{
  return x;
}

norettype_old2()
{
  return ;
}

static norettype_old3(a)
     int **a;
{
  return **a;
}


noretnoarg(x) {
  return x;
}
