
//There's a problem with the merger when a parameter overlaps with a static local.


int fun1(int n)
{
  return n;
}

int qux()
{
  static int n = 3;
  return n;
}

int fun2()
{
  int n; //This local doesn't seem to cause any problems.
  return n;
}



int main() {
  return 0;
}
